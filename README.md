# C Malloc Implementation

By [Paul Chun](http://www.paulchun.com)

A malloc implementation in C which uses a segregated free list to maintain the free blocks with a first fit search (best fit and next best fit produced lower efficiency ratings), coalescing adjacent free blocks as well as having a varying heap extend size.

