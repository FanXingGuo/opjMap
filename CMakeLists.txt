cmake_minimum_required(VERSION 3.15)
project(minimap2 C)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -g -Wall -O2 -Wc++-compat -DHAVE_KALLOC")

# 检测SSE和NEON指令集
include(CheckCCompilerFlag)
if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm")
    set(ARM_NEON TRUE)
    add_definitions(-D_FILE_OFFSET_BITS=64 -fsigned-char)
    if(NOT CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64")
        add_definitions(-mfpu=neon)
    endif()
else()
    # SSE指令集配置
    check_c_compiler_flag("-msse2" HAS_SSE2)
    check_c_compiler_flag("-msse4.1" HAS_SSE4_1)

    if(HAS_SSE2)
        add_definitions(-msse2)
    endif()

    if(HAS_SSE4_1)
        add_definitions(-msse4.1)
    endif()
endif()

# 源文件列表
set(SRC_FILES
        src/kthread.c
        src/kalloc.c
        src/misc.c
        src/bseq.c
        src/sketch.c
        src/sdust.c
        src/options.c
        src/index.c
        src/lchain.c
        src/align.c
        src/hit.c
        src/seed.c
        src/map.c
        src/format.c
        src/pe.c
        src/esterr.c
        src/splitidx.c
        src/main.c
)

# 修改KSW2模块配置部分
if(ARM_NEON)
    list(APPEND SRC_FILES
            src/ksw2_extz2_sse.c
            src/ksw2_extd2_sse.c
            src/ksw2_exts2_sse.c
    )
    set_source_files_properties(
            src/ksw2_extz2_sse.c
            src/ksw2_extd2_sse.c
            src/ksw2_exts2_sse.c
            PROPERTIES COMPILE_FLAGS "-DKSW_SSE2_ONLY -D__SSE2__"
    )
else()
    # 为每个SSE版本创建单独的对象文件
    add_library(ksw2_sse2 OBJECT
            src/ksw2_extz2_sse.c
            src/ksw2_extd2_sse.c
            src/ksw2_exts2_sse.c
    )
    target_compile_options(ksw2_sse2 PRIVATE -msse2 -mno-sse4.1 -DKSW_SSE2_ONLY)

    add_library(ksw2_sse41 OBJECT
            src/ksw2_extz2_sse.c
            src/ksw2_extd2_sse.c
            src/ksw2_exts2_sse.c
    )
    target_compile_options(ksw2_sse41 PRIVATE -msse4.1 -DKSW_CPU_DISPATCH)

    list(APPEND SRC_FILES
            src/ksw2_ll_sse.c
            src/ksw2_dispatch.c
    )

    # 将对象文件添加到可执行文件
    add_executable(opjMap ${SRC_FILES} $<TARGET_OBJECTS:ksw2_sse2> $<TARGET_OBJECTS:ksw2_sse41>)
endif()



# 链接库
find_package(ZLIB REQUIRED)
find_package(Threads REQUIRED)
target_link_libraries(opjMap PRIVATE m ${CMAKE_THREAD_LIBS_INIT} ZLIB::ZLIB)

# 可选工具
if(NOT ARM_NEON)
    add_executable(sdust src/sdust.c src/kalloc.c)
    target_compile_definitions(sdust PRIVATE _SDUST_MAIN)
    target_link_libraries(sdust PRIVATE m ZLIB::ZLIB)

    add_executable(minimap2-lite src/example.c ${SRC_FILES})
    target_link_libraries(minimap2-lite PRIVATE m ${CMAKE_THREAD_LIBS_INIT} ZLIB::ZLIB)
endif()

# 包含目录
target_include_directories(opjMap PRIVATE src)
if(NOT ARM_NEON)
    target_include_directories(sdust PRIVATE src)
    target_include_directories(minimap2-lite PRIVATE src)
endif()

# 强制使用 -O0 优化级别并生成调试信息
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -O0 -g3")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -g3")
else()
    message(STATUS "For full debuggability, use -DCMAKE_BUILD_TYPE=Debug")
endif()