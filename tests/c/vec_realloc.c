// vec_realloc: grow a uniquely-owned u32 block via realloc (M1c).
// Discipline: malloc(n), fill [0,n) with indices, realloc to m=2*n,
// fill the extension [n,m) with indices, sum [0,m), free once.
// realloc preserves the prefix (value semantics); growth is
// explicitly initialized before any read, so the Base zero-fill
// convention is unobservable here (like malloc zero-init in vec_alloc).
// OOM is out of scope (unbounded convention: realloc never fails).
// Spec: return = sum of indices 0 .. 2*n-1 (wrapping u32).
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t vec_realloc(size_t n) {
  uint32_t *v = (uint32_t *)malloc(n * sizeof(uint32_t));
  for (size_t i = 0; i < n; i++) {
    v[i] = (uint32_t)i;
  }
  size_t m = n + n;
  v = (uint32_t *)realloc(v, m * sizeof(uint32_t));
  for (size_t j = n; j < m; j++) {
    v[j] = (uint32_t)j;
  }
  uint32_t s = 0;
  for (size_t k = 0; k < m; k++) {
    s += v[k];
  }
  free(v);
  return s;
}
