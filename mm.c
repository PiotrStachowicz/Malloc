/* Piotr Stachowicz 337942 */

/* Method name: Segregated explicit free list with optimized boundary tags */

/*
  Statistics:
  Weighted memory utilization: 82.6%
  Total memory utilization: 95.45%
  Instructions per operation: 3950
*/

/*
  Block structure

  FREE BLOCK:

  [HEADER (SIZE | FLAGS)]
  [NEXT NUMERICAL POINTER]
  [PREV NUMERICAL POINTER]
  [PAYLOAD]
  [PADDING]
  [FOOTER (SIZE | FLAGS)]

  USED BLOCK:
  [HEADER (SIZE | FLAGS)]
  [PAYLOAD]
  [PADDING]
*/

/* Abstract malloc workflow
  First, we search for free blok on each of lists using find_fit.
  Find_fit uses best fit strategy.
  1) If we do find a free block, remove it from correct list and mark it
    as USED.
  2) If we do not find a free block, resize the heap and mark the new space as
  USED.
*/

/* Abstract free workflow
  First, we analize the state of surrounding blocks, there are four cases:
  (Before adding to free list mark it as free)
  1) [USED] [OUR BLOCK] [USED]
    In this case we only add our block to the correct free list.
  2) [USED] [OUR BLOCK] [FREE]
    In this case we merge our block with next (physically) and add it to correct
  free list. 3) [FREE] [OUR BLOCK] [USED] Vice versa. 4) [FREE] [OUR BLOCK]
  [FREE] Merge all the blocks and add to correct free list.
*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* Do not change the following! */
#ifdef DRIVER
/* Create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

/* ----------=[ SEGREGATED FREE LISTS ]=---------- */

// NOTE: This was my previous approach, but it was pointed to me that it's
//    a bit shady, so I changed it.

// /* Points at first free block of size: */
// static word_t *root1_2; /* 1-2 Bytes */
// static word_t *root3;   /* 3 Bytes */
// static word_t *root4;   /* 4 Bytes */
// static word_t *root5_8; /* 5-8 Bytes */
// static word_t *root9_;  /* 9+ Bytes */

/* ----------=[ BOUNDARY TAG HANDLERS ]=---------- */

/* Returns size of block in bytes */
static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

/* Returns 1 if block is used */
static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

/* Returns 1 if block is free */
static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given FREE block's header calculates footer */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns header */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  if (flags & USED)
    *bt = size | flags;
  else {
    *bt = size;
    *bt_footer(bt) = size;
  }
}

/* ----------=[ OPTIMIZED BOUNDARY TAGS ]=---------- */

/* Returns block's previous block free flag */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

/* Clears block's previous block free flag */
static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

/* Sets block's previous block free flag */
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL */
static inline word_t *bt_next(word_t *bt) {
  if (bt == last)
    return NULL;

  return (void *)bt + bt_size(bt);
}

/* Returns address of previous block or NULL */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start || !bt_get_prevfree(bt))
    return NULL;

  return (void *)bt - bt_size(bt - 1);
}

/* ----------=[ EXPLICIT LISTS ]=---------- */

/* Returns numerical representation of pointer on 4Bytes,
  by using the fact that MAX_HEAP is 100MB and base address is 0x800000000 */
static inline word_t shrink_pointer(word_t *ptr) {
  /* NULL is represented as 0 */
  if (!ptr)
    return 0;

  /* Keep only offset from the start of the heap */
  return ((uintptr_t)ptr - 0x800000000);
}

/* Connects one block to another (as previous) */
static inline void connect_prev(word_t *bt, word_t *prev_bt) {
  *(bt + 2) = shrink_pointer(prev_bt);
}

/* Connects one block to another (as next) */
static inline void connect_next(word_t *bt, word_t *next_bt) {
  *(bt + 1) = shrink_pointer(next_bt);
}

/* Returns pointer to previous free block */
static inline word_t *free_bt_prev(word_t *bt) {
  if (*(bt + 2) == 0)
    return NULL;

  /* Retrieve the pointer */
  return (word_t *)(0x800000000 + *(bt + 2));
}

/* Returns pointer to next free block */
static inline word_t *free_bt_next(word_t *bt) {
  if (*(bt + 1) == 0)
    return NULL;

  /* Retrieve the pointer */
  return (word_t *)(0x800000000 + *(bt + 1));
}

/* Returns number associated with the correct free list for given size */
static inline int resolve_list(word_t space) {
  if (space <= 2)
    return 0;

  if (space == 3)
    return 1;

  if (space == 4)
    return 2;

  if (space <= 8)
    return 3;

  return 4;
}

/* Returns pointer to a pointer of correct list */
static inline word_t **get_root(int which) {
  uintptr_t base = 0x80000000c;

  return (word_t **)(base + which * sizeof(word_t *));
}

/* Adds block to correct list */
static inline void free_list_add(word_t *bt) {

  /* Get access to correct list */
  int which = resolve_list(bt_size(bt));
  word_t **root = get_root(which);

  /* If current list is empty, create it */
  if (!*root) {
    *root = bt;

    connect_next(bt, NULL);
    connect_prev(bt, NULL);

    return;
  }

  /* Else add block as new root */
  connect_prev(bt, NULL);
  connect_next(bt, *root);

  connect_prev(*root, bt);

  *root = bt;
}

/* Removes block from correct list */
static inline void free_list_remove(word_t *bt) {
  /* Get addresses of buddies */
  word_t *prev = free_bt_prev(bt);
  word_t *next = free_bt_next(bt);

  /* Get access to correct list */
  int which = resolve_list(bt_size(bt));
  word_t **root = get_root(which);

  /* Case 1 */
  if (prev && next) {
    connect_next(prev, next);
    connect_prev(next, prev);
  }
  /* Case 2 */
  else if (prev) {
    connect_next(prev, NULL);
  }
  /* Case 3*/
  else if (next) {
    connect_prev(next, NULL);
    *root = next;
  }
  /* Case 4 */
  else {
    *root = NULL;
  }
}

/* -----------=[ MISCELLANOUS PROCEDURES ]=----------- */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT) */
static inline size_t blksz(size_t size) {
  size_t space = sizeof(word_t) + size;

  return (space + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1);
}

/* Extends the heap by desired size */
static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);

  if (ptr == (void *)-1)
    return NULL;

  return ptr;
}

/* Initializes the heap */
int mm_init(void) {
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));

  if (!ptr)
    return -1;

  /* Initialize heap metadata */
  heap_start = NULL;
  heap_end = NULL;
  last = NULL;

  word_t **roots = morecore(blksz(sizeof(word_t *) * 5));

  if (!roots)
    return -1;

  /* Initialize free lists */
  for (int i = 0; i < 5; ++i)
    roots[i] = NULL;

  return 0;
}

/* --------------------=[ MALLOC ]=-------------------- */

#if 0
/* First fit startegy (Not ready for latest code upgrade) */
static word_t *find_fit(size_t reqsz) {
  word_t *head = root;
  size_t space = blksz(reqsz);

  while (head) {
    if (bt_size(head) >= space) {
      return head;
    }

    head = free_bt_next(head);
  }

  /* We found nothing! */
  return NULL;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  size_t space = blksz(reqsz);

  /* Find correct list */
  int start = resolve_list(space);

  word_t *result = NULL;

  /* Find best fit in every list starting from smallest correct list */
  for (int i = start; i < 5; ++i) {
    size_t best_size = MAX_HEAP + 1;
    word_t *head = *get_root(i);

    while (head) {
      /* If correct size and better, save it */
      if (bt_size(head) < best_size && bt_size(head) >= space) {
        best_size = bt_size(head);
        result = head;
      }

      /* Go further */
      head = free_bt_next(head);
    }

    return result;
  }

  return result;
}
#endif

/* Returns pointer to the payload of the new block */
void *malloc(size_t size) {
  if (size == 0)
    return NULL;

  /* Check if there is suitable block */
  word_t *ptr = find_fit(size);
  size_t space = blksz(size);

  /* If such block does not exist, extend heap */
  if (!ptr) {
    ptr = morecore(space);

    /* Heap ran out of space! */
    if (!ptr)
      return NULL;

    /* Edge case for first allocation */
    if (!heap_start)
      heap_start = ptr;

    /* Set new block's prev flag (if needed) */
    bt_flags prevfree = 0;

    if (last)
      prevfree = (bt_free(last) << 1);

    /* Set new last block */
    last = ptr;

    /* Mark block as used */
    bt_make(ptr, space, USED | prevfree);

    /* Set new heap end */
    heap_end = last + bt_size(last);

    return bt_payload(last);
  }

  /* If we do find a spot... */

  size_t old_size = bt_size(ptr);

  free_list_remove(ptr);

  /* Mark it as used */
  bt_make(ptr, space, USED);

  /* Split the block */
  if (old_size > space) {
    word_t *next = (void *)ptr + space;

    /* Mark "new" block as free */
    bt_make(next, old_size - space, FREE);

    free_list_add(next);

    if (ptr == last)
      last = next;
  }
  /* Edge case for ideal fit */
  else if (old_size == space) {
    word_t *next = bt_next(ptr);

    /* If next block exists, set it's prev flag */
    if (next)
      bt_clr_prevfree(next);
  }

  return bt_payload(ptr);
}

/* ----------=[ FREE ]=----------- */

/* Frees the desired memory (non-lazy coallescing)*/
void free(void *ptr) {
  if (!ptr)
    return;

  /* Get info about our block */
  word_t *header = bt_fromptr(ptr);
  size_t space = bt_size(header);

  /* Collect info about surroundings */
  word_t *prev_header = bt_prev(header);
  word_t *next_header = bt_next(header);

  /* Check which case we are dealing with */
  int32_t prev, next;

  prev = prev_header ? bt_used(prev_header) : 1;
  next = next_header ? bt_used(next_header) : 1;

  /* Case 1 */
  if (prev == 1 && next == 1) {
    if (next_header)
      bt_set_prevfree(next_header);
  }
  /* Case 2 */
  else if (prev == 1 && next == 0) {
    space += bt_size(next_header);

    if (next_header == last)
      last = header;

    free_list_remove(next_header);
  }
  /* Case 3 */
  else if (prev == 0 && next == 1) {
    space += bt_size(prev_header);

    if (header == last)
      last = prev_header;

    if (next_header)
      bt_set_prevfree(next_header);

    header = prev_header;

    free_list_remove(prev_header);
  }
  /* Case 4 */
  else {
    space += bt_size(prev_header) + bt_size(next_header);

    if (next_header == last)
      last = prev_header;

    header = prev_header;

    free_list_remove(prev_header);
    free_list_remove(next_header);
  }

  /* Free the block */
  bt_make(header, space, FREE);

  /* And add it back to the free list */
  free_list_add(header);
}

/* ----------=[ REALLOC ]=---------- */

/* Reallocates memory with the desired size */
void *realloc(void *old_ptr, size_t size) {
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  if (!old_ptr)
    return malloc(size);

  /* Collect information about our block */
  word_t *header = bt_fromptr(old_ptr);
  size_t old_size = bt_size(header);
  size_t space = blksz(size);
  bt_flags prevfree = bt_get_prevfree(header);

  // Note: THIS IS EVIL
  // ---------------------------------------------------------
  // word_t *next_header = bt_next(header);
  // /* Check wheter we can extend our block to neighbour */
  // if (next_header && bt_free(next_header)) {
  //   size_t next_size = bt_size(next_header);

  //   /* Check if we can fit our new block */
  //   size_t together_size = old_size + next_size;

  //   if (together_size >= space) {
  //     free_list_remove(next_header);
  //     bt_make(header, space, USED | prevfree);

  //     /* If we should split */
  //     if (together_size > space) {
  //       word_t *split_block = (void *)header + space;
  //       bt_make(split_block, together_size - space, FREE);

  //       free_list_add(split_block);

  //       /* Update last */
  //       if (last == next_header)
  //         last = split_block;
  //     }
  //     /* Perfect fit */
  //     else if (last == next_header)
  //       last = header;

  //     return bt_payload(header);
  //   }
  // }
  // ---------------------------------------------------------

  /* Edge case for shrinking */
  if (header == last && old_size >= space) {
    /* Shrinking */
    if (old_size > space) {
      word_t *split_block = (void *)header + space;

      bt_make(split_block, old_size - space, FREE);

      free_list_add(split_block);

      last = split_block;

      *header = space | USED | prevfree;
    }

    return old_ptr;
  }

  /* Edge case for being last block */
  if (header == last && old_size < space) {
    void *sentinel = morecore(space - old_size);

    if (!sentinel)
      return NULL;

    *header = space | USED | prevfree;

    return old_ptr;
  }

  /* (Worst Case Scenario) Allocate new block... */
  void *new_ptr = malloc(size);

  if (!new_ptr)
    return NULL;

  if (size < old_size)
    old_size = size;

  memcpy(new_ptr, old_ptr, old_size);

  free(old_ptr);

  return new_ptr;
}

/* ----------=[ CALLOC ]=---------- */

/* Allocates memory and zeroes it before returning */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* ----------=[ MM_CHECKHEAP ]=---------- */

/* Checks heap for potential errors */
/* Note: I did not use this for the final method, but it was very helpful
    for the earlier implementations! */
void mm_checkheap(int verbose) {
  if (verbose) {
    printf("-----------=[ HEAP INFO ]=-----------\n");
  }

  word_t *head = heap_start;

  while (head) {
    if (verbose) {
      printf("-----------=[ BLOCK INFO ]=-----------\n");
      printf("Block: [%p]\n", head);
      printf("State: [%d]\n", bt_used(head));
      printf("Prev free: [%d]\n", bt_get_prevfree(head));

      if (bt_free(head)) {
        printf("Prev: [%p]\n", free_bt_prev(head));
        printf("Next: [%p]\n", free_bt_next(head));
      }
    }

    /* Check if sizes match */
    if (bt_free(head))
      assert(*head == *bt_footer(head));

    head = bt_next(head);
  }
}
