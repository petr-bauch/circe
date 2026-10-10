// chacha20_block: ChaCha20 block function (K4, RFC 8439 §2.3).
// Discipline: `state` is the single `__restrict__` 16-word state
// (single-`&mut` containment — one live pointer, so the pair check
// passes with no oracle change; the verdict still confirms the
// attr). Working copy `x`, ten double-rounds of eight inlined
// quarter rounds (columns then diagonals — a 4-writer QR leaf could
// never pass the pair check, so the round is inlined), then the
// add-back over `state`. All arithmetic is wrapping unsigned;
// rotates are shift-or with folded `32 - n` amounts.
// Spec: state += 10 double-rounds, checked against §2.3.2.
#include <stddef.h>
#include <stdint.h>

#define ROTL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))
#define QR(x, a, b, c, d) \
  x[a] += x[b];           \
  x[d] ^= x[a];           \
  x[d] = ROTL(x[d], 16);  \
  x[c] += x[d];           \
  x[b] ^= x[c];           \
  x[b] = ROTL(x[b], 12);  \
  x[a] += x[b];           \
  x[d] ^= x[a];           \
  x[d] = ROTL(x[d], 8);   \
  x[c] += x[d];           \
  x[b] ^= x[c];           \
  x[b] = ROTL(x[b], 7)

void chacha20_block(uint32_t *__restrict state) {
  uint32_t x[16];
  for (size_t i = 0; i < 16; i++)
    x[i] = state[i];
  for (size_t r = 0; r < 10; r++) {
    QR(x, 0, 4, 8, 12);
    QR(x, 1, 5, 9, 13);
    QR(x, 2, 6, 10, 14);
    QR(x, 3, 7, 11, 15);
    QR(x, 0, 5, 10, 15);
    QR(x, 1, 6, 11, 12);
    QR(x, 2, 7, 8, 13);
    QR(x, 3, 4, 9, 14);
  }
  for (size_t i = 0; i < 16; i++)
    state[i] += x[i];
}
