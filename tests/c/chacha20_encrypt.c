// chacha20_encrypt: ChaCha20 stream encryption (K6, RFC 8439 §2.4.1).
// Discipline: key/nonce are `const __restrict__` reads (8/3 words),
// msg is the single `__restrict__` writer (nwords words), all lengths
// and indices are u32 (64-bit loop bounds stay out; no div/mul/rem —
// block offsets advance by adds, the tail is a subtraction). Outer
// `while` over full blocks: straight-line state setup (constants +
// key + counter+b + nonce), one call to the admitted K4
// `chacha20_block` leaf, one 16-word xor loop. Tail: same setup with
// the final counter, one call, one ntail-word xor loop guarded by
// `ntail != 0`. All arithmetic is wrapping unsigned.
// Spec: msg[i] ^= keystream[i] per §2.4.1, checked against §2.4.2.
#include <stddef.h>
#include <stdint.h>

void chacha20_block(uint32_t *__restrict state);

void chacha20_encrypt(const uint32_t *__restrict key, uint32_t counter,
                      const uint32_t *__restrict nonce,
                      uint32_t *__restrict msg, uint32_t nwords) {
  uint32_t state[16];
  uint32_t b, i, off;
  b = 0;
  off = 0;
  while (off + 16u <= nwords) {
    state[0] = 0x61707865u;
    state[1] = 0x3320646eu;
    state[2] = 0x79622d32u;
    state[3] = 0x6b206574u;
    state[4] = key[0];
    state[5] = key[1];
    state[6] = key[2];
    state[7] = key[3];
    state[8] = key[4];
    state[9] = key[5];
    state[10] = key[6];
    state[11] = key[7];
    state[12] = counter + b;
    state[13] = nonce[0];
    state[14] = nonce[1];
    state[15] = nonce[2];
    chacha20_block(state);
    for (i = 0; i < 16; i++)
      msg[off + i] ^= state[i];
    b += 1u;
    off += 16u;
  }
  uint32_t ntail = nwords - off;
  if (ntail != 0) {
    state[0] = 0x61707865u;
    state[1] = 0x3320646eu;
    state[2] = 0x79622d32u;
    state[3] = 0x6b206574u;
    state[4] = key[0];
    state[5] = key[1];
    state[6] = key[2];
    state[7] = key[3];
    state[8] = key[4];
    state[9] = key[5];
    state[10] = key[6];
    state[11] = key[7];
    state[12] = counter + b;
    state[13] = nonce[0];
    state[14] = nonce[1];
    state[15] = nonce[2];
    chacha20_block(state);
    for (i = 0; i < ntail; i++)
      msg[off + i] ^= state[i];
  }
}
