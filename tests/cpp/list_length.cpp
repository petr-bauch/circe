// list_length: read-only traversal of a raw-pointer singly-linked
// list (L-ptr second-shape corpus). Discipline: `Node` is a two-field
// struct (`int val`, `Node *next`); the entry takes the head pointer
// by value and returns the node count (`0` for the empty list). All
// nodes are caller-owned (the test driver builds the chain with
// `new`; the entry itself never allocates). The loop chases `cur`
// with an explicit `cur != nullptr` guard; a null dereference is
// loud. Cycles are out of scope (the contract assumes an acyclic
// chain; fuel bounds the chase as a backstop). The count is
// `unsigned long` (64-bit); the entry reads only `next` links —
// payloads are never touched.
// Spec: on exit the return equals the number of nodes reachable
// from `head` (`0` iff empty); memory is unmodified.
struct Node {
  int val;
  Node *next;
};

unsigned long list_length(Node *head) {
  unsigned long n = 0;
  Node *cur = head;
  while (cur != nullptr) {
    cur = cur->next;
    n = n + 1;
  }
  return n;
}
