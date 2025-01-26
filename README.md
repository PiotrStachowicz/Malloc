# Segregated List Malloc Implementation

## Overview

This project provides a custom memory allocator for C programs, implementing `malloc`, `free`, and `realloc` using **segregated free lists** with optimized boundary tags to optimize dynamic memory management. 

## Key Features

- **Segregated Free Lists**: Free blocks are categorized into predefined size classes of: 1-2, 3, 4, 5-8, 9+ Bytes.
- **Coalescing**: Adjacent free blocks are merged during free.
- **Alignment**: All returned memory blocks are aligned to 16-bytes.

## Time Complexity Analysis

- **`malloc`**: 
  - **O(1)** *amortized* when a suitable block is found in the corresponding size class's free list.
  - **O(log k)** in worst-case scenarios, where k is the number of size classes, as only the relevant size classes are searched (not the entire heap).
  
- **`find_fit` (block search)**:
  - Directly tied to `malloc`'s performance. Utilizes best-fit.

- **`free`**: 
  - **O(1)** for deallocation and list reinsertion (and merge).

## Implementation Details
Stated in mm.c file.

## Build
```make```

## Performance tests
```make grade```

