// list_rev: iterative in-place reversal of an index-encoded
// singly-linked list (J-slice corpus). Discipline: `data` (payloads)
// and `nxt` (successor indices) are `&` (single-reference triples
// each, oracle governance vacuous, verdict honestly `unknown`);
// `head` is the entry index and `n` doubles as node count and end
// sentinel (`u64`, the G-track cursor convention — no signed
// sentinel, no new arithmetic). The loop chases `cur` through `nxt`:
// read `nxt[cur]` (widened into `nxt_cur`), rewire `nxt[cur]` to the
// predecessor, advance. All loop variables are seed-initialized
// (`nxt_cur = 0`, the G5a init-all-loop-vars convention — keeps the
// model environment uniform). `data` is deliberately untouched by the loop
// (payload-agnosticism is part of the spec story, pinned by golden
// edges). Cyclic input is not structurally excluded — fuel bounds
// the chase (the S3a fuel contract: exhaustion aborts loud). Every
// vector op sits behind its own fused `ult` guard (the bound checks
// live in the `at()` callees; the loop itself carries no literals
// and no branches). Misses and `nsw` overflow are loud (the bound
// checks live in the `at()` callees; the advances are pure wrapping
// `u64`).
// Spec: return = new head index (`n` for the empty list); on exit
// `nxt` holds the reversed links. OOB is loud.
#include <vector>

unsigned long list_rev(std::vector<int> &data, std::vector<int> &nxt, unsigned long head, unsigned long n) {
  unsigned long prev = n;
  unsigned long cur = head;
  unsigned long nxt_cur = 0;
  while (cur != n) {
    unsigned long nxt_cur = nxt.at(cur);
    nxt.at(cur) = (int)prev;
    prev = cur;
    cur = nxt_cur;
  }
  return prev;
}
