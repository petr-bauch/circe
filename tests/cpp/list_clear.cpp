// list_clear: free the whole chain (P1 fifth shape, whole-chain
// deallocation). Discipline: `Node` is a two-field struct
// (`int val`, `Node *next`); the entry takes the head pointer
// (caller-owned, possibly null) and chases with a single cursor,
// saving the link before each `free(cur)`, freeing every node
// exactly once, and returning the (now empty) head `nullptr`.
// The single pointer param needs no `__restrict__`
// (single-pointer exemption). The payload is never read and
// the freed cells are never chased — the link is saved before
// the free, so the dead cells stay untouched. Faults are
// loud, not branched: dereferencing or freeing a null,
// missing, or already-freed cell aborts in the model
// (`memLoad`/`memFree` miss/tag/liveness checks), exactly the
// L-ptr miss discipline — the corpus carries no explicit
// checks. Cycles are out of scope (the contract assumes an
// acyclic input chain). Spec: on exit every node of the input
// chain is freed (live flag cleared, contents kept but
// unusable), every other cell is untouched.
#include <stdlib.h>

struct Node {
  int val;
  Node *next;
};

Node *list_clear(Node *head) {
  Node *cur = head;
  while (cur != nullptr) {
    Node *next = cur->next;
    free(cur);
    cur = next;
  }
  return nullptr;
}
