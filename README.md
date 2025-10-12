====================================================================

opjMap                             2025/10/12  
ver1.0.0                           Wuhan, China  
		    	 	       
====================================================================  

System Requirements
===================

Software Requirements
---------------------
The opjMap is supported on the following operating systems

Linux 


Memory Requirements/Recommendations
-------------------------------------
opjMap  requires approximately
800 M of available disk space on the drive or partition.

opjMap requires a minimum of
16G of RAM for mapping sequence datasets to large reference genomes.


User's Guide
=================

Input Sequences Requirements
----------------------------
Input file requires fasta or fastq format

Execute Step
------------
Step 1: compile codes using make command  
Step 2: ./opjMap [options] <target.fa>|<target.idx> [query.fa] [...]

Running example
-----------
normal mapping  
`./opjMap -a genome.fna  query.fa -k 15  -t 32  -o opjmap.sam`  
mapping duplications  
`./opjMap -a genome.fna  query.fa -k 15  -t 32 -P -o opjmap.sam`

The final mapping result is opjmap.sam in SAM format.


Copyright Notice
===================
Software, documentation and related materials:  
Copyright (c) 2025-2029  
Wuhan Technology And Business University,China  
All rights reserved.  
