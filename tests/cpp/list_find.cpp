// list_find: return the first matching node (P1 third shape,
// read-only traversal leg reusing the chase kit). Discipline:
// `Node` is a two-field struct (`int val`, `Node *next`); the
// entry takes the head pointer (caller-owned, possibly null)
// and the payload, chases with a single cursor, and returns
// the first node whose payload matches — `nullptr` on miss
// (or empty input). The single pointer param needs no
// `__restrict__` (single-pointer exemption). The function is
// read-only by design: no stores to the chain, no `malloc`,
// no `free` — the loop guard, not a branch, covers misses.
// Faults are loud, not branched: dereferencing a null,
// missing, or dead cell aborts in the model (`memLoad`
// miss/tag/liveness checks), exactly the L-ptr miss
// discipline — the corpus carries no explicit checks. Cycles
// are out of scope (the contract assumes an acyclic input
// chain). Spec: on exit the returned pointer is the first
// chain node holding the payload, or null; memory is
// untouched.
struct Node {
  int val;
  Node *next;
};

Node *list_find(Node *head, int val) {
  Node *cur = head;
  while (cur != nullptr) {
    if (cur->val == val) {
      return cur;
    }
    cur = cur->next;
  }
  return nullptr;
}
