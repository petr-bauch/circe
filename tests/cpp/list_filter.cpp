// list_filter: unlink every matching node and free it (P1 remove-if
// shape, multi-drop leg). Discipline: `Node` is a two-field struct
// (`int val`, `Node *next`); the entry takes the head pointer
// (caller-owned, possibly null) and the payload, chases with a
// trailing pointer, unlinks every node whose payload matches
// (`head` case vs interior case), frees each victim exactly once,
// and returns the (possibly new) head. Survivors keep their
// relative order — a match advances only the cursor, a keep
// advances both. The single pointer param needs no
// `__restrict__` (single-pointer exemption). Miss legs are
// silent by design: no match (or empty input) returns the head
// untouched with no `free` — the loop guard, not a branch,
// covers them. Faults are loud, not branched: freeing a null,
// missing, or already-freed cell aborts in the model
// (`memFree` miss/tag/liveness checks), exactly the L-ptr miss
// discipline — the corpus carries no explicit checks. Cycles are
// out of scope (the contract assumes an acyclic input chain).
// Spec: on exit the returned chain holds exactly the input
// payloads that differ from `val`, in order; every matching
// cell is freed (live flag cleared, contents kept but
// unusable — any later dereference misses loudly), all other
// cells untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *list_filter(Node *head, int val) {
  Node *prev = nullptr;
  Node *cur = head;
  while (cur != nullptr) {
    if (cur->val == val) {
      Node *next = cur->next;
      if (prev == nullptr) {
        head = next;
      } else {
        prev->next = next;
      }
      free(cur);
      cur = next;
    } else {
      prev = cur;
      cur = cur->next;
    }
  }
  return head;
}
