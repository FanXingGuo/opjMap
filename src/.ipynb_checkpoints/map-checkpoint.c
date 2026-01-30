#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <errno.h>
#include <math.h>

#include "kthread.h"
#include "kvec.h"
#include "kalloc.h"
#include "sdust.h"
#include "mmpriv.h"
#include "bseq.h"
#include "khash.h"
#include <stdbool.h>  // 必须包含此头文件
#include <time.h>
// 定义 max 和 min 宏
#define max(a, b) ((a) > (b) ? (a) : (b))
#define min(a, b) ((a) < (b) ? (a) : (b))
#define globK 9
// 确保有基数排序支持
// #include "ksort.h"
static int cmp_wind(const void *a, const void *b) {
	return ((mm128_mt*)a)->wind - ((mm128_mt*)b)->wind;
}


static int cmp_idxPos(const void *a, const void *b) {
	return ((idxPos*)a)->idx - ((idxPos*)b)->idx;
}

// 降序比较函数（关键点：b - a 实现从大到小排序）
int compare_descending(const void *a, const void *b) {
	return ((idxPos*)b)->freq - ((idxPos*)a)->freq;
}
int compareIdxDe(const void *a, const void *b) {
	idxPos *pa=*(idxPos**)a;
	idxPos *pb=*(idxPos**)b;
	return pb->freq - pa->freq;
}
int compareFreDe(const void *a, const void *b) {
	idxPos *pa=(idxPos*)a;
	idxPos *pb=(idxPos*)b;
	return pb->freq - pa->freq;
}
int compareIdxAc(const void *a, const void *b) {
	idxPos *pa=(idxPos*)a;
	idxPos *pb=(idxPos*)b;
	return pa->idx - pb->idx;
}
// int compareIdx2Ac(const void *a, const void *b) {
// 	idxPos *pa=*(idxPos**)a;
// 	idxPos *pb=*(idxPos**)b;
// 	return pa->ref_id - pb->ref_id;
// }
// int compareIdx3Ac(const void *a, const void *b) {
// 	idxPos *pa=*(idxPos**)a;
// 	idxPos *pb=*(idxPos**)b;
// 	return pa->st - pb->st;
// }
int compareIdx2De(const void *a, const void *b) {
	idxPos *pa=*(idxPos**)a;
	idxPos *pb=*(idxPos**)b;
	return pa->ref_idx - pb->ref_idx;
}


mm_tbuf_t *mm_tbuf_init(void)
{
	mm_tbuf_t *b;
	b = (mm_tbuf_t*)calloc(1, sizeof(mm_tbuf_t));
	if (!(mm_dbg_flag & 1)) b->km = km_init();
	return b;
}

void mm_tbuf_destroy(mm_tbuf_t *b)
{
	if (b == 0) return;
	km_destroy(b->km);
	free(b);
}

void *mm_tbuf_get_km(mm_tbuf_t *b)
{
	return b->km;
}

static int mm_dust_minier(void *km, int n, mm128_t *a, int l_seq, const char *seq, int sdust_thres)
{
	int n_dreg, j, k, u = 0;
	const uint64_t *dreg;
	sdust_buf_t *sdb;
	if (sdust_thres <= 0) return n;
	sdb = sdust_buf_init(km);
	dreg = sdust_core((const uint8_t*)seq, l_seq, sdust_thres, 64, &n_dreg, sdb);
	for (j = k = 0; j < n; ++j) { // squeeze out minimizers that significantly overlap with LCRs
		int32_t qpos = (uint32_t)a[j].y>>1, span = a[j].x&0xff;
		int32_t s = qpos - (span - 1), e = s + span;
		while (u < n_dreg && (int32_t)dreg[u] <= s) ++u;
		if (u < n_dreg && (int32_t)(dreg[u]>>32) < e) {
			int v, l = 0;
			for (v = u; v < n_dreg && (int32_t)(dreg[v]>>32) < e; ++v) { // iterate over LCRs overlapping this minimizer
				int ss = s > (int32_t)(dreg[v]>>32)? s : dreg[v]>>32;
				int ee = e < (int32_t)dreg[v]? e : (uint32_t)dreg[v];
				l += ee - ss;
			}
			if (l <= span>>1) a[k++] = a[j]; // keep the minimizer if less than half of it falls in masked region
		} else a[k++] = a[j];
	}
	sdust_buf_destroy(sdb);
	return k; // the new size
}

static void collect_minimizers(void *km, const mm_mapopt_t *opt, const mm_idx_t *mi, int n_segs, const int *qlens, const char **seqs, mm128_v *mv)
{
	int i, n, sum = 0;
	mv->n = 0;
	for (i = n = 0; i < n_segs; ++i) {
		size_t j;
		mm_sketch(km, seqs[i], qlens[i], mi->w, mi->k, i, mi->flag&MM_I_HPC, mv);
		for (j = n; j < mv->n; ++j)
			mv->a[j].y += sum << 1;
		if (opt->sdust_thres > 0) // mask low-complexity minimizers
			mv->n = n + mm_dust_minier(km, mv->n - n, mv->a + n, qlens[i], seqs[i], opt->sdust_thres);
		sum += qlens[i], n = mv->n;
	}
}

#include "ksort.h"
#define heap_lt(a, b) ((a).x > (b).x)
KSORT_INIT(heap, mm128_t, heap_lt)

static inline int skip_seed(int flag, uint64_t r, const mm_seed_t *q, const char *qname, int qlen, const mm_idx_t *mi, int *is_self)
{
	*is_self = 0;
	if (qname && (flag & (MM_F_NO_DIAG|MM_F_NO_DUAL))) {
		const mm_idx_seq_t *s = &mi->seq[r>>32];
		int cmp;
		cmp = strcmp(qname, s->name);
		if ((flag&MM_F_NO_DIAG) && cmp == 0 && (int)s->len == qlen) {
			if ((uint32_t)r>>1 == (q->q_pos>>1)) return 1; // avoid the diagnonal anchors
			if ((r&1) == (q->q_pos&1)) *is_self = 1; // this flag is used to avoid spurious extension on self chain
		}
		if ((flag&MM_F_NO_DUAL) && cmp > 0) // all-vs-all mode: map once
			return 1;
	}
	if (flag & (MM_F_FOR_ONLY|MM_F_REV_ONLY)) {
		if ((r&1) == (q->q_pos&1)) { // forward strand
			if (flag & MM_F_REV_ONLY) return 1;
		} else {
			if (flag & MM_F_FOR_ONLY) return 1;
		}
	}
	return 0;
}

static mm128_t *collect_seed_hits_heap(void *km, const mm_mapopt_t *opt, int max_occ, const mm_idx_t *mi, const char *qname, const mm128_v *mv, int qlen, int64_t *n_a, int *rep_len,
								  int *n_mini_pos, uint64_t **mini_pos)
{
	int i, n_m, heap_size = 0;
	int64_t j, n_for = 0, n_rev = 0;
	mm_seed_t *m;
	mm128_t *a, *heap;

	m = mm_collect_matches(km, &n_m, qlen, max_occ, opt->max_max_occ, opt->occ_dist, mi, mv, n_a, rep_len, n_mini_pos, mini_pos);

	heap = (mm128_t*)kmalloc(km, n_m * sizeof(mm128_t));
	a = (mm128_t*)kmalloc(km, *n_a * sizeof(mm128_t));

	for (i = 0, heap_size = 0; i < n_m; ++i) {
		if (m[i].n > 0) {
			heap[heap_size].x = m[i].cr[0];
			heap[heap_size].y = (uint64_t)i<<32;
			++heap_size;
		}
	}
	ks_heapmake_heap(heap_size, heap);
	while (heap_size > 0) {
		mm_seed_t *q = &m[heap->y>>32];
		mm128_t *p;
		uint64_t r = heap->x;
		int32_t is_self, rpos = (uint32_t)r >> 1;
		if (!skip_seed(opt->flag, r, q, qname, qlen, mi, &is_self)) {
			if ((r&1) == (q->q_pos&1)) { // forward strand
				p = &a[n_for++];
				p->x = (r&0xffffffff00000000ULL) | rpos;
				p->y = (uint64_t)q->q_span << 32 | q->q_pos >> 1;
			} else { // reverse strand
				p = &a[(*n_a) - (++n_rev)];
				p->x = 1ULL<<63 | (r&0xffffffff00000000ULL) | rpos;
				p->y = (uint64_t)q->q_span << 32 | (qlen - ((q->q_pos>>1) + 1 - q->q_span) - 1);
			}
			p->y |= (uint64_t)q->seg_id << MM_SEED_SEG_SHIFT;
			if (q->is_tandem) p->y |= MM_SEED_TANDEM;
			if (is_self) p->y |= MM_SEED_SELF;
		}
		// update the heap
		if ((uint32_t)heap->y < q->n - 1) {
			++heap[0].y;
			heap[0].x = m[heap[0].y>>32].cr[(uint32_t)heap[0].y];
		} else {
			heap[0] = heap[heap_size - 1];
			--heap_size;
		}
		ks_heapdown_heap(0, heap_size, heap);
	}
	kfree(km, m);
	kfree(km, heap);

	// reverse anchors on the reverse strand, as they are in the descending order
	for (j = 0; j < n_rev>>1; ++j) {
		mm128_t t = a[(*n_a) - 1 - j];
		a[(*n_a) - 1 - j] = a[(*n_a) - (n_rev - j)];
		a[(*n_a) - (n_rev - j)] = t;
	}
	if (*n_a > n_for + n_rev) {
		memmove(a + n_for, a + (*n_a) - n_rev, n_rev * sizeof(mm128_t));
		*n_a = n_for + n_rev;
	}
	return a;
}

static mm128_t *collect_seed_hits(void *km, const mm_mapopt_t *opt, int max_occ, const mm_idx_t *mi, const char *qname, const mm128_v *mv, int qlen, int64_t *n_a, int *rep_len,
								  int *n_mini_pos, uint64_t **mini_pos)
{
	int i, n_m;
	mm_seed_t *m;
	mm128_t *a;
	m = mm_collect_matches(km, &n_m, qlen, max_occ, opt->max_max_occ, opt->occ_dist, mi, mv, n_a, rep_len, n_mini_pos, mini_pos);
	a = (mm128_t*)kmalloc(km, *n_a * sizeof(mm128_t));
	for (i = 0, *n_a = 0; i < n_m; ++i) {
		mm_seed_t *q = &m[i];
		const uint64_t *r = q->cr;
		uint32_t k;
		for (k = 0; k < q->n; ++k) {
			int32_t is_self, rpos = (uint32_t)r[k] >> 1;
			mm128_t *p;
			if (skip_seed(opt->flag, r[k], q, qname, qlen, mi, &is_self)) continue;
			p = &a[(*n_a)++];
			if ((r[k]&1) == (q->q_pos&1)) { // forward strand
				p->x = (r[k]&0xffffffff00000000ULL) | rpos;
				p->y = (uint64_t)q->q_span << 32 | q->q_pos >> 1;
			} else if (!(opt->flag & MM_F_QSTRAND)) { // reverse strand and not in the query-strand mode
				p->x = 1ULL<<63 | (r[k]&0xffffffff00000000ULL) | rpos;
				p->y = (uint64_t)q->q_span << 32 | (qlen - ((q->q_pos>>1) + 1 - q->q_span) - 1);
			} else { // reverse strand; query-strand
				int32_t len = mi->seq[r[k]>>32].len;
				p->x = 1ULL<<63 | (r[k]&0xffffffff00000000ULL) | (len - (rpos + 1 - q->q_span) - 1); // coordinate only accurate for non-HPC seeds
				p->y = (uint64_t)q->q_span << 32 | q->q_pos >> 1;
			}
			p->y |= (uint64_t)q->seg_id << MM_SEED_SEG_SHIFT;
			if (q->is_tandem) p->y |= MM_SEED_TANDEM;
			if (is_self) p->y |= MM_SEED_SELF;
		}
	}
	kfree(km, m);
	radix_sort_128x(a, a + (*n_a));
	return a;
}

static void chain_post(const mm_mapopt_t *opt, int max_chain_gap_ref, const mm_idx_t *mi, void *km, int qlen, int n_segs, const int *qlens, int *n_regs, mm_reg1_t *regs, mm128_t *a)
{
	if (!(opt->flag & MM_F_ALL_CHAINS)) { // don't choose primary mapping(s)
		mm_set_parent(km, opt->mask_level, opt->mask_len, *n_regs, regs, opt->a * 2 + opt->b, opt->flag&MM_F_HARD_MLEVEL, opt->alt_drop);
		if (n_segs <= 1) mm_select_sub(km, opt->pri_ratio, mi->k*2, opt->best_n, 1, opt->max_gap * 0.8, n_regs, regs);
		else mm_select_sub_multi(km, opt->pri_ratio, 0.2f, 0.7f, max_chain_gap_ref, mi->k*2, opt->best_n, n_segs, qlens, n_regs, regs);
	}
}

static mm_reg1_t *align_regs(const mm_mapopt_t *opt, const mm_idx_t *mi, void *km, int qlen, const char *seq, int *n_regs, mm_reg1_t *regs, mm128_t *a)
{
	if (!(opt->flag & MM_F_CIGAR)) return regs;
	regs = mm_align_skeleton(km, opt, mi, qlen, seq, n_regs, regs, a); // this calls mm_filter_regs()
	if (!(opt->flag & MM_F_ALL_CHAINS)) { // don't choose primary mapping(s)
		mm_set_parent(km, opt->mask_level, opt->mask_len, *n_regs, regs, opt->a * 2 + opt->b, opt->flag&MM_F_HARD_MLEVEL, opt->alt_drop);
		mm_select_sub(km, opt->pri_ratio, mi->k*2, opt->best_n, 0, opt->max_gap * 0.8, n_regs, regs);
		mm_set_sam_pri(*n_regs, regs);
	}
	return regs;
}
// 从 4-bit 压缩序列解码单个碱基
static inline char mm_idx_getbase(const mm_idx_t *mi, int tid, int pos) {
	uint32_t *S = mi->S;
	uint64_t offset = mi->seq[tid].offset;
	uint8_t base = (S[(offset + pos) / 8] >> (4 * ((offset + pos) % 8))) & 0xF;
	return "ACGTN"[base];
}
// 提取参考序列区间 [st, ed] 的字符序列
char* mm_extract_ref_region(const mm_idx_t *mi, int tid, int st, int ed) {
	if (tid < 0 || tid >= mi->n_seq || !mi->S) return NULL;

	uint32_t len = mi->seq[tid].len;
	if (st < 0) st = 0;
	if (ed >= len) ed = len - 1;
	int frag_len = ed - st + 1;

	char *seq = (char*)malloc(frag_len + 1);
	for (int i = 0; i < frag_len; ++i) {
		seq[i] = mm_idx_getbase(mi, tid, st + i);
	}
	seq[frag_len] = '\0';
	// printf("Extracted region [%d-%d], length=%d, first 10 bases: %.10s\n",
	// 	   st, ed, frag_len, seq);
	return seq; // 需调用者 free(seq)
}
// 提取参考区间 [tid, st, ed] 的 minimizer
void mm_collect_ref_minimizers(
	const mm_idx_t *mi,
	int tid, int st, int ed,
	int k, int w,
	mm128_v *mv,
	void *km,
	size_t lastn
) {
	uint32_t len = mi->seq[tid].len;
	if (st < 0) st = 0;
	if (ed >= len) ed = len - 1;
	// 1. 提取参考序列片段
	char *seq = mm_extract_ref_region(mi, tid, st, ed);
	if (!seq) return;

	// 2. 生成 minimizer（注意：需调整坐标到全局参考坐标系）
	int frag_len = ed - st + 1;
	mm_sketch(km, seq, frag_len, w, k, tid, 0, mv); // is_hpc=0

	// 3. 调整 minimizer 的坐标（从局部片段坐标转为全局参考坐标）
	// 调整 minimizer 的坐标（局部 -> 全局）
	for (size_t i = lastn == 0 ? 0 : lastn; i < mv->n; ++i) {
		uint64_t y = mv->a[i].y;
		uint32_t pos = (uint32_t)y>>1;       // 提取低32位位置
		uint64_t strand = y & 1;        // 提取最高位（链信息）
		uint64_t new_pos = st + pos-1;      // 全局坐标
		mv->a[i].y =(y&0xFFFFFFFF00000000ULL)|(new_pos<<1|strand);

		//mv->a[i].y=(st+mv->a[i].y>>1)<<1|mv->a[i].y>>63;
		//mv->a[i].y+=st;

	}

	free(seq);
}
void print_continuous_regions(const mm_idx_t *mi,int tid,int seql,int k, int w,mm128_v *mv,
	void *km,const mm128_mt *aa, int32_t n_a) {
	if (n_a == 0) return;  // 空数组直接返回

	int32_t start = aa[0].x;  // 起始位置
	uint32_t current_wind = aa[0].wind;  // 当前wind值
	uint32_t expected_next_wind = current_wind + 1;  // 期望的下一个wind值
	int n=0;
	int oft=seql*0.2;
	for (int32_t i = 1; i < n_a; i++) {
		if (aa[i].wind == current_wind) {
			// 相同wind，继续
			continue;
		} else if (aa[i].wind == expected_next_wind) {
			// wind连续，更新期望值
			current_wind = aa[i].wind;
			expected_next_wind = current_wind + 1;
		} else {
			// wind不连续，打印当前区间
			//printf("\n%d -> %d\n", (int32_t)start, (int32_t)aa[i-1].x);
			mm_collect_ref_minimizers(mi, 0, max(0,(int32_t)start-oft), min((int32_t)aa[i-1].x+oft,mi->seq[0].len), k, 1, mv, km,n);
			n=mv->n;
			// 重置为新的区间
			start = aa[i].x;
			current_wind = aa[i].wind;
			expected_next_wind = current_wind + 1;
		}
	}

	// 打印最后一个区间
	// printf("%d -> %d\n", (int32_t)start, (int32_t)aa[n_a-1].x);
	mm_collect_ref_minimizers(mi, 0, max(0,(int32_t)start-oft), min((int32_t)aa[n_a-1].x+oft,mi->seq[0].len), k, 1, mv, km,n);
}
void mm_map_frag(const mm_idx_t *mi, int n_segs, const int *qlens, const char **seqs, int *n_regs, mm_reg1_t **regs, mm_tbuf_t *b, const mm_mapopt_t *opt, const char *qname)
{
	int i, j, rep_len, qlen_sum, n_regs0, n_mini_pos;
	int max_chain_gap_qry, max_chain_gap_ref, is_splice = !!(opt->flag & MM_F_SPLICE), is_sr = !!(opt->flag & MM_F_SR);
	uint32_t hash;
	int64_t n_a;
	uint64_t *u, *mini_pos;
	mm128_t *a;
	mm128_v mv = {0,0,0};
	mm_reg1_t *regs0;
	km_stat_t kmst;
	float chn_pen_gap, chn_pen_skip;

	for (i = 0, qlen_sum = 0; i < n_segs; ++i)
		qlen_sum += qlens[i], n_regs[i] = 0, regs[i] = 0;

	if (qlen_sum == 0 || n_segs <= 0 || n_segs > MM_MAX_SEG) return;
	if (opt->max_qlen > 0 && qlen_sum > opt->max_qlen) return;

	hash  = qname && !(opt->flag & MM_F_NO_HASH_NAME)? __ac_X31_hash_string(qname) : 0;
	hash ^= __ac_Wang_hash(qlen_sum) + __ac_Wang_hash(opt->seed);
	hash  = __ac_Wang_hash(hash);

	collect_minimizers(b->km, opt, mi, n_segs, qlens, seqs, &mv);
	if (opt->q_occ_frac > 0.0f) mm_seed_mz_flt(b->km, &mv, opt->mid_occ, opt->q_occ_frac);
	if (opt->flag & MM_F_HEAP_SORT) a = collect_seed_hits_heap(b->km, opt, opt->mid_occ, mi, qname, &mv, qlen_sum, &n_a, &rep_len, &n_mini_pos, &mini_pos);
	else a = collect_seed_hits(b->km, opt, opt->mid_occ, mi, qname, &mv, qlen_sum, &n_a, &rep_len, &n_mini_pos, &mini_pos);

	if (mm_dbg_flag & MM_DBG_PRINT_SEED) {
		fprintf(stderr, "RS\t%d\n", rep_len);
		for (i = 0; i < n_a; ++i)
			fprintf(stderr, "SD\t%s\t%d\t%c\t%d\t%d\t%d\n", mi->seq[a[i].x<<1>>33].name, (int32_t)a[i].x, "+-"[a[i].x>>63], (int32_t)a[i].y, (int32_t)(a[i].y>>32&0xff),
					i == 0? 0 : ((int32_t)a[i].y - (int32_t)a[i-1].y) - ((int32_t)a[i].x - (int32_t)a[i-1].x));
	}

	if (0) { // print a
		printf("a all:");
		for (i = 0; i < n_a; ++i) {

			// if(0|((int32_t)a[i].x>158274114 && (int32_t)a[i].x<158277953)) {
			//printf( "(%d,%d,%d,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,a[i].x<<1>>33, (int32_t)(a[i].y>>32&0xff)); //d多个基因组
			 printf( "(%d,%d,%c,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,"10"[a[i].x>>63], (int32_t)(a[i].y>>32&0xff));
			//aa[ct++]=a[i];

		}
		printf("\n");
	}
	//printf("a,%d; ",n_a);
	bool op9m=false;
	if(n_a>0&1) {


		if (0) {
			for (i = 0; i < n_a; ++i) {
				printf( "(%d,%d,%c,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,"10"[a[i].x>>63], (int32_t)(a[i].y>>32&0xff));
			}
			printf("\n");
		}
		uint64_t sum_len=0;
		uint64_t * ref_cur=(uint64_t *)kmalloc(b->km,(mi->n_seq+1)*sizeof(uint64_t));

		ref_cur[0]=0;
		memset(ref_cur, 0, (mi->n_seq+1)*sizeof(uint64_t));
		for (i = 0; i < mi->n_seq; ++i) {
			ref_cur[i+1]=ref_cur[i]+mi->seq[i].len;
			sum_len+=(uint64_t)(mi->seq[i].len);
		}
		int windLen=(sum_len+qlens[0])/1.41421356/1000; //default bucket len 1000,~700bp,max ref length 1400billion bp

		bool* windBoolOpen = (bool*)kmalloc(b->km,windLen * sizeof(bool));
		memset(windBoolOpen, 0, windLen * sizeof(bool));

		// uint32_t* aw = (uint32_t*)kcalloc(b->km,n_a, sizeof(uint32_t));  // calloc会自动初始化为0
		// 1. 先申请存放两个指针的内存 (uint32_t**)
		uint32_t **aw = (uint32_t**)kmalloc(b->km, 2 * sizeof(uint32_t*));

		// 2. 申请实际的数据内存，大小为 2 * n_a，使用 kcalloc 自动初始化为0
		// 注意：这里将通过 aw[0] 持有整块内存的指针
		aw[0] = (uint32_t*)kcalloc(b->km, 2 * n_a, sizeof(uint32_t));
		// 3. 将第二行的指针指向内存的中间位置
		aw[1] = aw[0] + n_a;
		// 访问方式: aw[0][index] 或 aw[1][index]


		// int * wl2ws =(int *)kcalloc(b->km,windLen, sizeof(int));
		// memset(wl2ws, -1, windLen * sizeof(int));
		// 1. 申请指针数组
		int **wl2ws = (int**)kmalloc(b->km, 2 * sizeof(int*));
		// 2. 申请实际数据内存 (2 * windLen)
		// 这里用 kmalloc 即可，因为下面马上会 memset 覆盖
		wl2ws[0] = (int*)kmalloc(b->km, 2 * windLen * sizeof(int));
		// 3. 设置第二行指针
		wl2ws[1] = wl2ws[0] + windLen;
		// 4. 初始化整块内存为 -1
		// 注意：直接对 aw[0] 进行 memset，长度是 2 * windLen
		memset(wl2ws[0], -1, 2 * windLen * sizeof(int));

		// idxPos * naIdx=(idxPos*)kcalloc(b->km,n_a, sizeof(idxPos));
		// memset(naIdx, 0, n_a * sizeof(idxPos));
		// 1. 申请指针数组
		idxPos **naIdx = (idxPos**)kmalloc(b->km, 2 * sizeof(idxPos*));
		// 2. 申请实际数据内存 (2 * n_a)
		naIdx[0] = (idxPos*)kcalloc(b->km, 2 * n_a, sizeof(idxPos));
		// 3. 设置第二行指针
		naIdx[1] = naIdx[0] + n_a;
		// kcalloc 已经自动 memset 为 0 了，如果 idxPos 结构体比较复杂，确保 0 初始化是你要的效果
		memset(naIdx[0], 0, 2 * n_a * sizeof(idxPos)); // 这一句对于 kcalloc 是多余的，但保留也没错



		int ptrIdxCur=0;

		int ptrIdxCur2=0;
		int  naIdxPtr[]={0,0};
		idxPos * tmpIdx;
		int allocIdx2[]={0,0};
		uint64_t tempX=0;
		int gt2w=0; //window greater than 2,  num
		int ic=0;// idx choose
		idxPos *  idx2[]={&naIdx[0][0],&naIdx[1][0]};
		for (i = 0; i < n_a; ++i) {
			tempX=ref_cur[a[i].x<<1>>33]+(int32_t)a[i].x;
			aw[0][i]=(uint32_t)(0.5*(tempX-(int32_t)a[i].y+qlens[0])/1000);
			aw[1][i]=(uint32_t)(0.5*(tempX-(int32_t)a[i].y+qlens[0]+500)/1000); // 500, half of 100, 1/2 window
			// if((int32_t)a[i].x==17518792) {
			// 	printf("--");
			// }
			for (j =0; j < 2; ++j) {
				if(wl2ws[j][aw[j][i]]==-1) {
					wl2ws[j][aw[j][i]]=naIdxPtr[j]++;
					tmpIdx=&(naIdx[j][wl2ws[j][aw[j][i]]]);
					tmpIdx->freq=1;
					tmpIdx->idx=aw[j][i];
					tmpIdx->st=(int32_t)a[i].x;
					tmpIdx->ed=(int32_t)a[i].x;
					tmpIdx->ref_id=a[i].x<<1>>33;
				}
				else {
					tmpIdx=&(naIdx[j][wl2ws[j][aw[j][i]]]);
					tmpIdx->freq++;
					tmpIdx->st=min(tmpIdx->st,(int32_t)a[i].x);
					tmpIdx->ed=max(tmpIdx->ed,(int32_t)a[i].x);
				}
				if(tmpIdx->freq>idx2[j]->freq){
					idx2[j]=tmpIdx;
				}
				if(tmpIdx->freq==3) {
					allocIdx2[j]++;
				}
			}
		}
		ic=idx2[0]->freq>idx2[1]->freq?0:1;
		tmpIdx=idx2[ic];
		float top1Den=1;
		int topFreq=tmpIdx->freq;
		float dftop1den=1;
		float dflen=1;
		float dffreq=1;
		float dfd=1;
		int countGo=0;
		bool showif=false;
		bool justGo=false;
		idxPos * oneMaxIdx=NULL;
		top1Den=(float)tmpIdx->freq/(float)(tmpIdx->ed-tmpIdx->st);
		idxPos** ptrIdx=(idxPos**)kcalloc(b->km,allocIdx2[ic], sizeof(idxPos*));
		idxPos** ptrIdx2=(idxPos**)kcalloc(b->km,allocIdx2[ic], sizeof(idxPos*));// for select windows
		if(showif)qsort(naIdx[ic], naIdxPtr[ic], sizeof(idxPos), compareFreDe);
		if(showif)printf("w%s:",qname);
		oneMaxIdx=&naIdx[ic][0];
		for (i = 0; i < naIdxPtr[ic]; ++i) {
			tmpIdx=&(naIdx[ic][i]);
			if (tmpIdx->freq<=3) continue;
			dftop1den=((float)tmpIdx->freq/(float)(tmpIdx->ed-tmpIdx->st))/top1Den-1;
			dfd=max(0,1-dftop1den*dftop1den);
			dflen=(float)abs(qlens[0]-(min(3*(tmpIdx->ed-tmpIdx->st),qlens[0])))/qlens[0];
			if(showif)printf("(%d,%f),",tmpIdx->freq, dfd-dflen);
			tmpIdx->score=dfd-dflen;
			if(tmpIdx->score>0.1 && tmpIdx->freq>3) {
				ptrIdxCur++;
				ptrIdx2[ptrIdxCur2++]=tmpIdx;
			}
			if(tmpIdx->score>opt->win_weight) {
				tmpIdx->ref_idx=ref_cur[tmpIdx->ref_id]+tmpIdx->st;
				ptrIdx[countGo++]=tmpIdx;
			}
			if(tmpIdx->score>oneMaxIdx->score) {
				oneMaxIdx=tmpIdx;
			}
		}
		if(showif) {
			printf("\na:");
			for (i = 0; i < n_a; ++i) {
				printf( "(%d,%d,%c,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,"10"[a[i].x>>63], (int32_t)(a[i].y>>32&0xff));

			}
			printf("\n");
			printf("a2:");
			//qsort(naIdx[ic], naIdxPtr[ic], sizeof(idxPos), compareIdxAc);
			// for(i = 0; i < countGo; ++i) {
			// 	windBoolOpen[ptrIdx[i]->idx]=true;
			// }
			// for (i = 0; i < n_a; ++i) {
			// 	if(windBoolOpen[aw[ic][i]]) {
			// 		printf( "(%d,%d,%c,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,"10"[a[i].x>>63], (int32_t)(a[i].y>>32&0xff));
			// 	}
			// }
			// printf("\n");
		}

		// idxPos** ptrIdx2=(idxPos**)kcalloc(b->km,ptrIdxCur, sizeof(idxPos*));// for select windows

		mm128_v mv1 = {0, 0, 0}; // 存储 minimizer
		mm128_v mvQue={0,0,0};


		//if(countGo>1)printf("@o9m-%s\n",qname);
		// if(countGo>1) {
		// 	op9m=true;
		// 	countGo=1;
		// };
		if(countGo==1 ||opt->win_weight>=1.0) { // window level, rm noisy
			justGo=true;
			int nn_a=0,nnac=0;
			for (i = 0; i < ptrIdxCur2; ++i) {
				windBoolOpen[ptrIdx2[i]->idx]=true;
				nn_a+=ptrIdx2[i]->freq;
			}
			mm128_t *aa = (mm128_t*)kmalloc(b->km, (nn_a+5)* sizeof(mm128_t));//debug 多申请些空间，防止溢出写入
			for (i = 0; i < n_a; ++i) {
				if(windBoolOpen[aw[ic][i]]) {
					aa[nnac++]=a[i];
					if(showif)printf( "(%d,%d,%c,%d),",  (int32_t)a[i].x, (int32_t)a[i].y,"10"[a[i].x>>63], (int32_t)(a[i].y>>32&0xff));
				}
			}
			if(showif)printf("\n");
			mm128_t *tmp=a;
			a=aa;
			n_a=nn_a;
			kfree(b->km,tmp);
		}else{
		// if(countGo>1){
			//9mer
			//ref
			// printf("@o9m-%s\n",qname);
			op9m=true;

			if(showif)printf("w%s:",qname);
			if(showif)justGo=true;
			qsort(ptrIdx, countGo, sizeof(idxPos*), compareIdx2De);
			int64_t ist=0,ied=0;
			if (countGo > 0) {
				// 1. 初始化当前合并区间的状态，从第0个元素开始
				int64_t cur_st = ptrIdx[0]->st;
				int64_t cur_ed = ptrIdx[0]->ed;
				int32_t cur_ref = ptrIdx[0]->ref_id;

				// 2. 从第1个元素开始遍历
				for (int i = 1; i < countGo; i++) {
					// 使用指针访问当前元素，写法为 ptrIdx2[i]
					idxPos *next_node = ptrIdx[i];
					// 判断是否可以合并：
					// 条件1: ref_id 必须相同
					// 条件2: 下一个的起始位置(st) 必须落在当前累计的区间内(<= cur_ed)
					if (next_node->ref_id == cur_ref && next_node->st <= cur_ed) {
						// --- 执行合并 ---
						// 如果下一个元素的结束位置比当前记录的更远，则扩展区间
						if (next_node->ed > cur_ed) {
							cur_ed = next_node->ed;
						}
						// 注意：st 不需要变，因为已经排序过，之前的st肯定是最小的
					} else {
						// --- 无法合并，输出之前的区间 ---
						// 调用函数写入之前累计的结果
						mm_collect_ref_minimizers(mi, cur_ref, cur_st, cur_ed, 9, 9, &mv1, b->km, mv1.n);
						// --- 重置状态为当前元素，开始新的区间 ---
						cur_st = next_node->st;
						cur_ed = next_node->ed;
						cur_ref = next_node->ref_id;
					}
				}

				// 3. 循环结束后，处理并输出最后一个缓存的区间
				mm_collect_ref_minimizers(mi, cur_ref, cur_st, cur_ed, 9, 9, &mv1, b->km, mv1.n);
			}

			radix_sort_128x(mv1.a, mv1.a + mv1.n);
			// 提取que的minimizer
			mm_sketch(b->km, seqs[0], qlens[0], 1, globK, 0, 0, &mvQue); // is_hpc=0
			// printf("seq=%s\n",seqs[0]);
			radix_sort_128x(mvQue.a, mvQue.a + mvQue.n);
			//寻找锚点
			//写s了位置先试试
			//计算sumA
			int curRef=0,curRead=0,sumA=0;
			int m=0;
			// 这里是重新提取的kmer，然后匹配
			while (curRef<mv1.n&&curRead<mvQue.n) {
				if (mv1.a[curRef].x>>8 == mvQue.a[curRead].x>>8) {
					m=0;
					while (curRef+m<mv1.n && mv1.a[curRef+m].x>>8 == mvQue.a[curRead].x>>8) {
						sumA+=1;
						m+=1;
					}
					if (curRead<mvQue.n-1) {
						curRead+=1;
					}else {
						break;
					}
				}
				if (mvQue.a[curRead].x>mv1.a[curRef].x) {
					if(curRef<mv1.n-1) {
						curRef+=1;
					}
					else {
						break;
					}
				}
				if (mv1.a[curRef].x > mvQue.a[curRead].x) {
					curRead+=1;
				}
			}
			int allN=n_a+sumA;
			mm128_t *aaa = (mm128_t*)kmalloc(b->km, (sumA+5)* sizeof(mm128_t));
			// mm128_t *aaa = (mm128_t*)kmalloc(b->km, (allN+5)* sizeof(mm128_t));

			curRef=0,curRead=0,m=0;
			// ct=sumAnchMP;
			int ct=0;

			// for (i = 0; i < n_a; ++i) {
			// 	aaa[ct++]=a[i];
			// }


			mm128_mt tp={0,0,0};
			int k9_wind=0;
			while (curRef<mv1.n&&curRead<mvQue.n) {
				if ((mv1.a[curRef].x)>>8 == (mvQue.a[curRead].x)>>8) {
					m=0;
					while (curRef+m<mv1.n && mv1.a[curRef+m].x>>8 == mvQue.a[curRead].x>>8) {
						 /*printf("(%d,%d,%c,%lu),", (int32_t)mv1.a[curRef].y>>1, (int32_t)mvQue.a[curRead].y>>1,
				 			"01"[(mvQue.a[curRead].y<<63==mv1.a[curRef].y<<63)],mv1.a[curRef+m].x);*/

						mm128_t tp = {0, 0};  // 初始化
						uint32_t query_pos = (mvQue.a[curRead].y >> 1) & 0xFFFFFFFF;
						uint32_t ref_pos = (mv1.a[curRef + m].y <<32>>33) & 0xFFFFFFFF;
						// uint32_t ref_pos = (mv1.a[curRef + m].y >> 1) & 0xFFFFFFFF;
						uint64_t rid = mv1.a[curRef + m].y & 0xFFFFFFFF00000000ULL;
						// uint64_t rid = mv1.a[curRef + m].y & 0xFFFFFFFF00000000ULL;
						// if(rid!=0) {
						// 	printf("!");
						// }
						// if(ref_pos==54020820) {
						// 	// printf("123");
						// }
						// if (1&&((mvQue.a[curRead].y)<<63 ==0) && ((mv1.a[curRef + m].y)<<63==0 )) { // 正链
						// if (1&&((mvQue.a[curRead].y)<<63 ) == ((mv1.a[curRef + m].y)<<63 )) { // 正链
						if (((mvQue.a[curRead].y) & 1) == ((mv1.a[curRef + m].y) & 1)) { // 正链
							tp.x = rid | ref_pos;  // 参考序列ID + 位置
							tp.y = (uint64_t)globK << 32 | query_pos;  // 跨度k + 查询位置
							//k9_wind=(uint32_t)(0.5*((int32_t)tp.x-(int32_t)tp.y+mi->seq[0].len)/1000);
							// if (!windBoolP[k9_wind]) {
							// 	m+=1;
							// 	continue;
							// }
							//aaa[ct++]=tp;
						} else { // 反链
							tp.x = 1ULL << 63 | rid | ref_pos;  // 标记反向链
							tp.y = (uint64_t)globK << 32 | (qlens[0] - (query_pos+1-globK) - 1);  // 查询位置反向互补
							//tp.y = (uint64_t)globK << 32 | query_pos;  // 跨度k + 查询位置
							//k9_wind=a[i].wind=(uint32_t)(0.5*((int32_t)tp.x-(int32_t)tp.y+mi->seq[0].len)/1000);
							// if(!windBoolM[k9_wind]) {
							// 	m+=1;
							// 	continue;
							// }
						}
						// printf("(%d,%d,%c),", (int32_t)tp.x, (int32_t)tp.y,
						// 	 "01"[tp.x>>63]);

						 aaa[ct++]=tp;
						//tp=(mm128_t){0,0,0};
						m+=1;
					}
					if (curRead<mvQue.n-1) {
						curRead+=1;
					}else {
						break;
					}
				}
				if ((mv1.a[curRef].x)>>8 < (mvQue.a[curRead].x)>>8) {
				// if (mvQue.a[curRead].x>mv1.a[curRef].x) {
					if(curRef<mv1.n-1) {
						curRef+=1;
					}
					else {
						break;
					}
				}
				if ((mv1.a[curRef].x)>>8 > (mvQue.a[curRead].x)>>8) {
					curRead+=1;
				}
			}


			mm128_t *tmp=a;
			a=aaa;
			n_a=ct;
			//radix_sort_128xy(a, a + n_a);
			radix_sort_128x(a, a + n_a);


			kfree(b->km,tmp);

			// 释放内存
			kfree(b->km, mv1.a);
			kfree(b->km, mvQue.a);

			//justGo=true;

		}



		// kfree(b->km, wl2ws);
		// kfree(b->km,naIdx);
		// kfree(b->km,aw);
		// 释放 aw
		kfree(b->km, aw[0]); // 先释放数据块
		kfree(b->km, aw);    // 再释放指针数组

		// 释放 wl2ws
		kfree(b->km, wl2ws[0]);
		kfree(b->km, wl2ws);

		// 释放 naIdx
		kfree(b->km, naIdx[0]);
		kfree(b->km, naIdx);


		kfree(b->km,ptrIdx);
		kfree(b->km,ptrIdx2);
		kfree(b->km,windBoolOpen);
		kfree(b->km,ref_cur);
	}





	// set max chaining gap on the query and the reference sequence
	if (is_sr)
		max_chain_gap_qry = qlen_sum > opt->max_gap? qlen_sum : opt->max_gap;
	else max_chain_gap_qry = opt->max_gap;
	if (opt->max_gap_ref > 0) {
		max_chain_gap_ref = opt->max_gap_ref; // always honor mm_mapopt_t::max_gap_ref if set
	} else if (opt->max_frag_len > 0) {
		max_chain_gap_ref = opt->max_frag_len - qlen_sum;
		if (max_chain_gap_ref < opt->max_gap) max_chain_gap_ref = opt->max_gap;
	} else max_chain_gap_ref = opt->max_gap;
	if(op9m) {
		chn_pen_gap  = opt->chain_gap_scale * 1.1 * mi->k; //mini 0.01
		chn_pen_skip = opt->chain_skip_scale * 1.1 * mi->k; //mini 0.01
	}else {
		chn_pen_gap  = opt->chain_gap_scale * 0.01 * mi->k; //mini 0.01
		chn_pen_skip = opt->chain_skip_scale * 0.01 * mi->k; //mini 0.01
	}

	if (opt->flag & MM_F_RMQ) {
		a = mg_lchain_rmq(opt->max_gap, opt->rmq_inner_dist, opt->bw, opt->max_chain_skip, opt->rmq_size_cap, opt->min_cnt, opt->min_chain_score,
						  chn_pen_gap, chn_pen_skip, n_a, a, &n_regs0, &u, b->km);
	} else {
		a = mg_lchain_dp(max_chain_gap_ref, max_chain_gap_qry, opt->bw, opt->max_chain_skip, opt->max_chain_iter, opt->min_cnt,
			opt->min_chain_score,
						 chn_pen_gap, chn_pen_skip, is_splice, n_segs, n_a, a, &n_regs0, &u, b->km);
	}

	if (opt->bw_long > opt->bw && (opt->flag & (MM_F_SPLICE|MM_F_SR|MM_F_NO_LJOIN)) == 0 && n_segs == 1 && n_regs0 > 1) { // re-chain/long-join for long sequences
		int32_t st = (int32_t)a[0].y, en = (int32_t)a[(int32_t)u[0] - 1].y;
		if (qlen_sum - (en - st) > opt->rmq_rescue_size || en - st > qlen_sum * opt->rmq_rescue_ratio) {
			int32_t i;
			for (i = 0, n_a = 0; i < n_regs0; ++i) n_a += (int32_t)u[i];
			kfree(b->km, u);
			radix_sort_128x(a, a + n_a);
			a = mg_lchain_rmq(opt->max_gap, opt->rmq_inner_dist, opt->bw_long, opt->max_chain_skip, opt->rmq_size_cap, opt->min_cnt,
				opt->min_chain_score,
							  chn_pen_gap, chn_pen_skip, n_a, a, &n_regs0, &u, b->km);
		}
	} else if (opt->max_occ > opt->mid_occ && rep_len > 0 && !(opt->flag & MM_F_RMQ)) { // re-chain, mostly for short reads
		int rechain = 0;
		if (n_regs0 > 0) { // test if the best chain has all the segments
			int n_chained_segs = 1, max = 0, max_i = -1, max_off = -1, off = 0;
			for (i = 0; i < n_regs0; ++i) { // find the best chain
				if (max < (int)(u[i]>>32)) max = u[i]>>32, max_i = i, max_off = off;
				off += (uint32_t)u[i];
			}
			for (i = 1; i < (int32_t)u[max_i]; ++i) // count the number of segments in the best chain
				if ((a[max_off+i].y&MM_SEED_SEG_MASK) != (a[max_off+i-1].y&MM_SEED_SEG_MASK))
					++n_chained_segs;
			if (n_chained_segs < n_segs)
				rechain = 1;
		} else rechain = 1;
		if (rechain) { // redo chaining with a higher max_occ threshold
			kfree(b->km, a);
			kfree(b->km, u);
			kfree(b->km, mini_pos);
			if (opt->flag & MM_F_HEAP_SORT) a = collect_seed_hits_heap(b->km, opt, opt->max_occ, mi, qname, &mv, qlen_sum, &n_a, &rep_len, &n_mini_pos, &mini_pos);
			else a = collect_seed_hits(b->km, opt, opt->max_occ, mi, qname, &mv, qlen_sum, &n_a, &rep_len, &n_mini_pos, &mini_pos);
			a = mg_lchain_dp(max_chain_gap_ref, max_chain_gap_qry, opt->bw, opt->max_chain_skip, opt->max_chain_iter, opt->min_cnt, opt->min_chain_score,
							 chn_pen_gap, chn_pen_skip, is_splice, n_segs, n_a, a, &n_regs0, &u, b->km);
		}
	}
	b->frag_gap = max_chain_gap_ref;
	b->rep_len = rep_len;

	regs0 = mm_gen_regs(b->km, hash, qlen_sum, n_regs0, u, a, !!(opt->flag&MM_F_QSTRAND));
	if (mi->n_alt) {
		mm_mark_alt(mi, n_regs0, regs0);
		mm_hit_sort(b->km, &n_regs0, regs0, opt->alt_drop); // this step can be merged into mm_gen_regs(); will do if this shows up in profile
	}

	if (mm_dbg_flag & (MM_DBG_PRINT_SEED|MM_DBG_PRINT_CHAIN))
		for (j = 0; j < n_regs0; ++j)
			for (i = regs0[j].as; i < regs0[j].as + regs0[j].cnt; ++i)
				fprintf(stderr, "CN\t%d\t%s\t%d\t%c\t%d\t%d\t%d\n", j, mi->seq[a[i].x<<1>>33].name, (int32_t)a[i].x, "+-"[a[i].x>>63], (int32_t)a[i].y, (int32_t)(a[i].y>>32&0xff),
						i == regs0[j].as? 0 : ((int32_t)a[i].y - (int32_t)a[i-1].y) - ((int32_t)a[i].x - (int32_t)a[i-1].x));

	chain_post(opt, max_chain_gap_ref, mi, b->km, qlen_sum, n_segs, qlens, &n_regs0, regs0, a);
	if (!is_sr && !(opt->flag&MM_F_QSTRAND)) {
		mm_est_err(mi, qlen_sum, n_regs0, regs0, a, n_mini_pos, mini_pos);
		n_regs0 = mm_filter_strand_retained(n_regs0, regs0);
	}

	if (n_segs == 1) { // uni-segment
		regs0 = align_regs(opt, mi, b->km, qlens[0], seqs[0], &n_regs0, regs0, a);
		regs0 = (mm_reg1_t*)realloc(regs0, sizeof(*regs0) * n_regs0);
		mm_set_mapq(b->km, n_regs0, regs0, opt->min_chain_score, opt->a, rep_len, is_sr);
		n_regs[0] = n_regs0, regs[0] = regs0;
	} else { // multi-segment
		mm_seg_t *seg;
		seg = mm_seg_gen(b->km, hash, n_segs, qlens, n_regs0, regs0, n_regs, regs, a); // split fragment chain to separate segment chains
		free(regs0);
		for (i = 0; i < n_segs; ++i) {
			mm_set_parent(b->km, opt->mask_level, opt->mask_len, n_regs[i], regs[i], opt->a * 2 + opt->b, opt->flag&MM_F_HARD_MLEVEL, opt->alt_drop); // update mm_reg1_t::parent
			regs[i] = align_regs(opt, mi, b->km, qlens[i], seqs[i], &n_regs[i], regs[i], seg[i].a);
			mm_set_mapq(b->km, n_regs[i], regs[i], opt->min_chain_score, opt->a, rep_len, is_sr);
		}
		mm_seg_free(b->km, n_segs, seg);
		if (n_segs == 2 && opt->pe_ori >= 0 && (opt->flag&MM_F_CIGAR))
			mm_pair(b->km, max_chain_gap_ref, opt->pe_bonus, opt->a * 2 + opt->b, opt->a, qlens, n_regs, regs); // pairing
	}

	kfree(b->km, mv.a);
	kfree(b->km, a);
	kfree(b->km, u);
	kfree(b->km, mini_pos);

	if (b->km) {
		km_stat(b->km, &kmst);
		if (mm_dbg_flag & MM_DBG_PRINT_QNAME)
			fprintf(stderr, "QM\t%s\t%d\tcap=%ld,nCore=%ld,largest=%ld\n", qname, qlen_sum, kmst.capacity, kmst.n_cores, kmst.largest);
		assert(kmst.n_blocks == kmst.n_cores); // otherwise, there is a memory leak
		if (kmst.largest > 1U<<28 || (opt->cap_kalloc > 0 && kmst.capacity > opt->cap_kalloc)) {
			if (mm_dbg_flag & MM_DBG_PRINT_QNAME)
				fprintf(stderr, "[W::%s] reset thread-local memory after read %s\n", __func__, qname);
			km_destroy(b->km);
			b->km = km_init();
		}
	}
}

mm_reg1_t *mm_map(const mm_idx_t *mi, int qlen, const char *seq, int *n_regs, mm_tbuf_t *b, const mm_mapopt_t *opt, const char *qname)
{
	mm_reg1_t *regs;
	mm_map_frag(mi, 1, &qlen, &seq, n_regs, &regs, b, opt, qname);
	return regs;
}

/**************************
 * Multi-threaded mapping *
 **************************/

typedef struct {
	int n_processed, n_threads, n_fp;
	int64_t mini_batch_size;
	const mm_mapopt_t *opt;
	mm_bseq_file_t **fp;
	const mm_idx_t *mi;
	kstring_t str;

	int n_parts;
	uint32_t *rid_shift;
	FILE *fp_split, **fp_parts;
} pipeline_t;

typedef struct {
	const pipeline_t *p;
    int n_seq, n_frag;
	mm_bseq1_t *seq;
	int *n_reg, *seg_off, *n_seg, *rep_len, *frag_gap;
	mm_reg1_t **reg;
	mm_tbuf_t **buf;
} step_t;

static void worker_for(void *_data, long i, int tid) // kt_for() callback
{
    step_t *s = (step_t*)_data;
	int qlens[MM_MAX_SEG], j, off = s->seg_off[i], pe_ori = s->p->opt->pe_ori;
	const char *qseqs[MM_MAX_SEG];
	double t = 0.0;
	mm_tbuf_t *b = s->buf[tid];
	assert(s->n_seg[i] <= MM_MAX_SEG);
	if (mm_dbg_flag & MM_DBG_PRINT_QNAME) {
		fprintf(stderr, "QR\t%s\t%d\t%d\n", s->seq[off].name, tid, s->seq[off].l_seq);
		t = realtime();
	}
	for (j = 0; j < s->n_seg[i]; ++j) {
		if (s->n_seg[i] == 2 && ((j == 0 && (pe_ori>>1&1)) || (j == 1 && (pe_ori&1))))
			mm_revcomp_bseq(&s->seq[off + j]);
		qlens[j] = s->seq[off + j].l_seq;
		qseqs[j] = s->seq[off + j].seq;
	}
	if (s->p->opt->flag & MM_F_INDEPEND_SEG) {
		for (j = 0; j < s->n_seg[i]; ++j) {
			mm_map_frag(s->p->mi, 1, &qlens[j], &qseqs[j], &s->n_reg[off+j], &s->reg[off+j], b, s->p->opt, s->seq[off+j].name);
			s->rep_len[off + j] = b->rep_len;
			s->frag_gap[off + j] = b->frag_gap;
		}
	} else {
		mm_map_frag(s->p->mi, s->n_seg[i], qlens, qseqs, &s->n_reg[off], &s->reg[off], b, s->p->opt, s->seq[off].name);
		for (j = 0; j < s->n_seg[i]; ++j) {
			s->rep_len[off + j] = b->rep_len;
			s->frag_gap[off + j] = b->frag_gap;
		}
	}
	for (j = 0; j < s->n_seg[i]; ++j) // flip the query strand and coordinate to the original read strand
		if (s->n_seg[i] == 2 && ((j == 0 && (pe_ori>>1&1)) || (j == 1 && (pe_ori&1)))) {
			int k, t;
			mm_revcomp_bseq(&s->seq[off + j]);
			for (k = 0; k < s->n_reg[off + j]; ++k) {
				mm_reg1_t *r = &s->reg[off + j][k];
				t = r->qs;
				r->qs = qlens[j] - r->qe;
				r->qe = qlens[j] - t;
				r->rev = !r->rev;
			}
		}
	if (mm_dbg_flag & MM_DBG_PRINT_QNAME)
		fprintf(stderr, "QT\t%s\t%d\t%.6f\n", s->seq[off].name, tid, realtime() - t);
}

static void merge_hits(step_t *s)
{
	int f, i, k0, k, max_seg = 0, *n_reg_part, *rep_len_part, *frag_gap_part, *qlens;
	void *km;
	FILE **fp = s->p->fp_parts;
	const mm_mapopt_t *opt = s->p->opt;

	km = km_init();
	for (f = 0; f < s->n_frag; ++f)
		max_seg = max_seg > s->n_seg[f]? max_seg : s->n_seg[f];
	qlens = CALLOC(int, max_seg + s->p->n_parts * 3);
	n_reg_part = qlens + max_seg;
	rep_len_part = n_reg_part + s->p->n_parts;
	frag_gap_part = rep_len_part + s->p->n_parts;
	for (f = 0, k = k0 = 0; f < s->n_frag; ++f) {
		k0 = k;
		for (i = 0; i < s->n_seg[f]; ++i, ++k) {
			int j, l, t, rep_len = 0;
			qlens[i] = s->seq[k].l_seq;
			for (j = 0, s->n_reg[k] = 0; j < s->p->n_parts; ++j) {
				mm_err_fread(&n_reg_part[j],    sizeof(int), 1, fp[j]);
				mm_err_fread(&rep_len_part[j],  sizeof(int), 1, fp[j]);
				mm_err_fread(&frag_gap_part[j], sizeof(int), 1, fp[j]);
				s->n_reg[k] += n_reg_part[j];
				if (rep_len < rep_len_part[j])
					rep_len = rep_len_part[j];
			}
			s->reg[k] = CALLOC(mm_reg1_t, s->n_reg[k]);
			for (j = 0, l = 0; j < s->p->n_parts; ++j) {
				for (t = 0; t < n_reg_part[j]; ++t, ++l) {
					mm_reg1_t *r = &s->reg[k][l];
					uint32_t capacity;
					mm_err_fread(r, sizeof(mm_reg1_t), 1, fp[j]);
					r->rid += s->p->rid_shift[j];
					if (opt->flag & MM_F_CIGAR) {
						mm_err_fread(&capacity, 4, 1, fp[j]);
						r->p = (mm_extra_t*)calloc(capacity, 4);
						r->p->capacity = capacity;
						mm_err_fread(r->p, r->p->capacity, 4, fp[j]);
					}
				}
			}
			if (!(opt->flag&MM_F_SR) && s->seq[k].l_seq >= opt->rank_min_len)
				mm_update_dp_max(s->seq[k].l_seq, s->n_reg[k], s->reg[k], opt->rank_frac, opt->a, opt->b);
			for (j = 0; j < s->n_reg[k]; ++j) {
				mm_reg1_t *r = &s->reg[k][j];
				if (r->p) r->p->dp_max2 = 0; // reset ->dp_max2 as mm_set_parent() doesn't clear it; necessary with mm_update_dp_max()
				r->subsc = 0; // this may not be necessary
				r->n_sub = 0; // n_sub will be an underestimate as we don't see all the chains now, but it can't be accurate anyway
			}
			mm_hit_sort(km, &s->n_reg[k], s->reg[k], opt->alt_drop);
			mm_set_parent(km, opt->mask_level, opt->mask_len, s->n_reg[k], s->reg[k], opt->a * 2 + opt->b, opt->flag&MM_F_HARD_MLEVEL, opt->alt_drop);
			if (!(opt->flag & MM_F_ALL_CHAINS)) {
				mm_select_sub(km, opt->pri_ratio, s->p->mi->k*2, opt->best_n, 0, opt->max_gap * 0.8, &s->n_reg[k], s->reg[k]);
				mm_set_sam_pri(s->n_reg[k], s->reg[k]);
			}
			mm_set_mapq(km, s->n_reg[k], s->reg[k], opt->min_chain_score, opt->a, rep_len, !!(opt->flag & MM_F_SR));
		}
		if (s->n_seg[f] == 2 && opt->pe_ori >= 0 && (opt->flag&MM_F_CIGAR))
			mm_pair(km, frag_gap_part[0], opt->pe_bonus, opt->a * 2 + opt->b, opt->a, qlens, &s->n_reg[k0], &s->reg[k0]);
	}
	free(qlens);
	km_destroy(km);
}

static void *worker_pipeline(void *shared, int step, void *in)
{
	int i, j, k;
    pipeline_t *p = (pipeline_t*)shared;
    if (step == 0) { // step 0: read sequences
		int with_qual = (!!(p->opt->flag & MM_F_OUT_SAM) && !(p->opt->flag & MM_F_NO_QUAL));
		int with_comment = !!(p->opt->flag & MM_F_COPY_COMMENT);
		int frag_mode = (p->n_fp > 1 || !!(p->opt->flag & MM_F_FRAG_MODE));
        step_t *s;
        s = (step_t*)calloc(1, sizeof(step_t));
		if (p->n_fp > 1) s->seq = mm_bseq_read_frag2(p->n_fp, p->fp, p->mini_batch_size, with_qual, with_comment, &s->n_seq);
		else s->seq = mm_bseq_read3(p->fp[0], p->mini_batch_size, with_qual, with_comment, frag_mode, &s->n_seq);
		if (s->seq) {
			s->p = p;
			for (i = 0; i < s->n_seq; ++i)
				s->seq[i].rid = p->n_processed++;
			s->buf = (mm_tbuf_t**)calloc(p->n_threads, sizeof(mm_tbuf_t*));
			for (i = 0; i < p->n_threads; ++i)
				s->buf[i] = mm_tbuf_init();
			s->n_reg = (int*)calloc(5 * s->n_seq, sizeof(int));
			s->seg_off = s->n_reg + s->n_seq; // seg_off, n_seg, rep_len and frag_gap are allocated together with n_reg
			s->n_seg = s->seg_off + s->n_seq;
			s->rep_len = s->n_seg + s->n_seq;
			s->frag_gap = s->rep_len + s->n_seq;
			s->reg = (mm_reg1_t**)calloc(s->n_seq, sizeof(mm_reg1_t*));
			for (i = 1, j = 0; i <= s->n_seq; ++i)
				if (i == s->n_seq || !frag_mode || !mm_qname_same(s->seq[i-1].name, s->seq[i].name)) {
					s->n_seg[s->n_frag] = i - j;
					s->seg_off[s->n_frag++] = j;
					j = i;
				}
			return s;
		} else free(s);
    } else if (step == 1) { // step 1: map
		if (p->n_parts > 0) merge_hits((step_t*)in);
		else kt_for(p->n_threads, worker_for, in, ((step_t*)in)->n_frag);
		return in;
    } else if (step == 2) { // step 2: output
		void *km = 0;
        step_t *s = (step_t*)in;
		const mm_idx_t *mi = p->mi;
		for (i = 0; i < p->n_threads; ++i) mm_tbuf_destroy(s->buf[i]);
		free(s->buf);
		if ((p->opt->flag & MM_F_OUT_CS) && !(mm_dbg_flag & MM_DBG_NO_KALLOC)) km = km_init();
		for (k = 0; k < s->n_frag; ++k) {
			int seg_st = s->seg_off[k], seg_en = s->seg_off[k] + s->n_seg[k];
			for (i = seg_st; i < seg_en; ++i) {
				mm_bseq1_t *t = &s->seq[i];
				if (p->opt->split_prefix && p->n_parts == 0) { // then write to temporary files
					mm_err_fwrite(&s->n_reg[i],    sizeof(int), 1, p->fp_split);
					mm_err_fwrite(&s->rep_len[i],  sizeof(int), 1, p->fp_split);
					mm_err_fwrite(&s->frag_gap[i], sizeof(int), 1, p->fp_split);
					for (j = 0; j < s->n_reg[i]; ++j) {
						mm_reg1_t *r = &s->reg[i][j];
						mm_err_fwrite(r, sizeof(mm_reg1_t), 1, p->fp_split);
						if (p->opt->flag & MM_F_CIGAR) {
							mm_err_fwrite(&r->p->capacity, 4, 1, p->fp_split);
							mm_err_fwrite(r->p, r->p->capacity, 4, p->fp_split);
						}
					}
				} else if (s->n_reg[i] > 0) { // the query has at least one hit
					for (j = 0; j < s->n_reg[i]; ++j) {
						mm_reg1_t *r = &s->reg[i][j];
						assert(!r->sam_pri || r->id == r->parent);
						if ((p->opt->flag & MM_F_NO_PRINT_2ND) && r->id != r->parent)
							continue;
						if (p->opt->flag & MM_F_OUT_SAM)
							mm_write_sam3(&p->str, mi, t, i - seg_st, j, s->n_seg[k], &s->n_reg[seg_st], (const mm_reg1_t*const*)&s->reg[seg_st], km, p->opt->flag, s->rep_len[i]);
						else
							mm_write_paf3(&p->str, mi, t, r, km, p->opt->flag, s->rep_len[i]);
						mm_err_puts(p->str.s);
					}
				} else if ((p->opt->flag & MM_F_PAF_NO_HIT) || ((p->opt->flag & MM_F_OUT_SAM) && !(p->opt->flag & MM_F_SAM_HIT_ONLY))) { // output an empty hit, if requested
					if (p->opt->flag & MM_F_OUT_SAM)
						mm_write_sam3(&p->str, mi, t, i - seg_st, -1, s->n_seg[k], &s->n_reg[seg_st], (const mm_reg1_t*const*)&s->reg[seg_st], km, p->opt->flag, s->rep_len[i]);
					else
						mm_write_paf3(&p->str, mi, t, 0, 0, p->opt->flag, s->rep_len[i]);
					mm_err_puts(p->str.s);
				}
			}
			for (i = seg_st; i < seg_en; ++i) {
				for (j = 0; j < s->n_reg[i]; ++j) free(s->reg[i][j].p);
				free(s->reg[i]);
				free(s->seq[i].seq); free(s->seq[i].name);
				if (s->seq[i].qual) free(s->seq[i].qual);
				if (s->seq[i].comment) free(s->seq[i].comment);
			}
		}
		free(s->reg); free(s->n_reg); free(s->seq); // seg_off, n_seg, rep_len and frag_gap were allocated with reg; no memory leak here
		km_destroy(km);
		if (mm_verbose >= 3)
			fprintf(stderr, "[M::%s::%.3f*%.2f] mapped %d sequences\n", __func__, realtime() - mm_realtime0, cputime() / (realtime() - mm_realtime0), s->n_seq);
		free(s);
	}
    return 0;
}

static mm_bseq_file_t **open_bseqs(int n, const char **fn)
{
	mm_bseq_file_t **fp;
	int i, j;
	fp = (mm_bseq_file_t**)calloc(n, sizeof(mm_bseq_file_t*));
	for (i = 0; i < n; ++i) {
		if ((fp[i] = mm_bseq_open(fn[i])) == 0) {
			if (mm_verbose >= 1)
				fprintf(stderr, "ERROR: failed to open file '%s': %s\n", fn[i], strerror(errno));
			for (j = 0; j < i; ++j)
				mm_bseq_close(fp[j]);
			free(fp);
			return 0;
		}
	}
	return fp;
}

int mm_map_file_frag(const mm_idx_t *idx, int n_segs, const char **fn, const mm_mapopt_t *opt, int n_threads)
{
	int i, pl_threads;
	pipeline_t pl;
	if (n_segs < 1) return -1;
	memset(&pl, 0, sizeof(pipeline_t));
	pl.n_fp = n_segs;
	pl.fp = open_bseqs(pl.n_fp, fn);
	if (pl.fp == 0) return -1;
	pl.opt = opt, pl.mi = idx;
	pl.n_threads = n_threads > 1? n_threads : 1;
	pl.mini_batch_size = opt->mini_batch_size;
	if (opt->split_prefix)
		pl.fp_split = mm_split_init(opt->split_prefix, idx);
	pl_threads = n_threads == 1? 1 : (opt->flag&MM_F_2_IO_THREADS)? 3 : 2;
	kt_pipeline(pl_threads, worker_pipeline, &pl, 3);

	free(pl.str.s);
	if (pl.fp_split) fclose(pl.fp_split);
	for (i = 0; i < pl.n_fp; ++i)
		mm_bseq_close(pl.fp[i]);
	free(pl.fp);
	return 0;
}

int mm_map_file(const mm_idx_t *idx, const char *fn, const mm_mapopt_t *opt, int n_threads)
{
	return mm_map_file_frag(idx, 1, &fn, opt, n_threads);
}

int mm_split_merge(int n_segs, const char **fn, const mm_mapopt_t *opt, int n_split_idx)
{
	int i;
	pipeline_t pl;
	mm_idx_t *mi;
	if (n_segs < 1 || n_split_idx < 1) return -1;
	memset(&pl, 0, sizeof(pipeline_t));
	pl.n_fp = n_segs;
	pl.fp = open_bseqs(pl.n_fp, fn);
	if (pl.fp == 0) return -1;
	pl.opt = opt;
	pl.mini_batch_size = opt->mini_batch_size;

	pl.n_parts = n_split_idx;
	pl.fp_parts  = CALLOC(FILE*, pl.n_parts);
	pl.rid_shift = CALLOC(uint32_t, pl.n_parts);
	pl.mi = mi = mm_split_merge_prep(opt->split_prefix, n_split_idx, pl.fp_parts, pl.rid_shift);
	if (pl.mi == 0) {
		free(pl.fp_parts);
		free(pl.rid_shift);
		return -1;
	}
	for (i = n_split_idx - 1; i > 0; --i)
		pl.rid_shift[i] = pl.rid_shift[i - 1];
	for (pl.rid_shift[0] = 0, i = 1; i < n_split_idx; ++i)
		pl.rid_shift[i] += pl.rid_shift[i - 1];
	if (opt->flag & MM_F_OUT_SAM)
		for (i = 0; i < (int32_t)pl.mi->n_seq; ++i)
			printf("@SQ\tSN:%s\tLN:%d\n", pl.mi->seq[i].name, pl.mi->seq[i].len);

	kt_pipeline(2, worker_pipeline, &pl, 3);

	free(pl.str.s);
	mm_idx_destroy(mi);
	free(pl.rid_shift);
	for (i = 0; i < n_split_idx; ++i)
		fclose(pl.fp_parts[i]);
	free(pl.fp_parts);
	for (i = 0; i < pl.n_fp; ++i)
		mm_bseq_close(pl.fp[i]);
	free(pl.fp);
	mm_split_rm_tmp(opt->split_prefix, n_split_idx);
	return 0;
}
