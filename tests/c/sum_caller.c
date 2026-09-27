// sum_caller: DAG call into bounded sum_array (S1).
// Discipline: a is __restrict__ + const with length n, single call to
// sum_array, return its result (caller adds nothing else).
// Spec: sum_caller(a,n) = sum of first n elements.
#include <stddef.h>
#include <stdint.h>

uint32_t sum_array(const uint32_t *__restrict a, size_t n);

uint32_t sum_caller(const uint32_t *__restrict a, size_t n) {
  return sum_array(a, n);
}
