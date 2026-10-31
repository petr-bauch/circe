// linked_reverse: iterative in-place reversal of a raw-pointer
// singly-linked list (L-slice corpus). Discipline: `Node` is a
// two-field struct (`int val`, `Node *next`); the entry takes the
// head pointer by value and returns the new head (`nullptr` for the
// empty list). All nodes are caller-owned (the test driver builds
// the chain with `new`; the entry itself never allocates —
// bump-region allocation lives in the driver, matching the
// caller-owned-buffers discipline). The loop chases `cur` with the
// classic three-pointer swing: read `cur->next`, swing
// `cur->next` to the predecessor, advance. Null checks are explicit
// (`cur != nullptr` guard); a null dereference is loud. Cycles are
// out of scope (the contract assumes an acyclic chain; fuel bounds
// the chase as a backstop).
// Spec: on exit the links run head-to-tail in reverse order with
// payloads untouched; return = old tail (`nullptr` iff empty).
struct Node {
  int val;
  Node *next;
};

Node *list_reverse(Node *head) {
  Node *prev = nullptr;
  Node *cur = head;
  while (cur != nullptr) {
    Node *nxt = cur->next;
    cur->next = prev;
    prev = cur;
    cur = nxt;
  }
  return prev;
}
