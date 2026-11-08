// list_unique: unlink every node equal to its predecessor and free
// it (P1 adjacent-duplicate squeeze, multi-drop leg). Discipline:
// `Node` is a two-field struct (`int val`, `Node *next`); the entry
// takes the head pointer (caller-owned, possibly null) and chases
// with a trailing pointer, unlinking every node whose payload
// equals its predecessor's (`prev == nullptr` keeps the head —
// the first node has no predecessor, so the head never swings
// and the entry returns it unchanged), freeing each victim
// exactly once. Survivors keep their relative order and hold
// exactly the input payloads with adjacent duplicates removed,
// on sorted or unsorted input alike (adjacency is local —
// sortedness is not assumed). The single pointer param needs no
// `__restrict__` (single-pointer exemption). Miss legs are
// silent by design: an empty, singleton, or duplicate-free chain
// returns the head untouched with no `free` — the loop guard,
// not a branch, covers them. Faults are loud, not branched:
// freeing a null, missing, or already-freed cell aborts in the
// model (`memFree` miss/tag/liveness checks), exactly the L-ptr
// miss discipline — the corpus carries no explicit checks.
// Cycles are out of scope (the contract assumes an acyclic input
// chain). Spec: on exit the returned chain holds exactly the
// input payloads with each equal run collapsed to its first
// element, in order; every dropped cell is freed (live flag
// cleared, contents kept but unusable — any later dereference
// misses loudly), all other cells untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *list_unique(Node *head) {
  Node *prev = nullptr;
  Node *cur = head;
  while (cur != nullptr) {
    if (prev != nullptr && cur->val == prev->val) {
      Node *next = cur->next;
      prev->next = next;
      free(cur);
      cur = next;
    } else {
      prev = cur;
      cur = cur->next;
    }
  }
  return head;
}
