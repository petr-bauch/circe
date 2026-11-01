// list_append: tail insertion into a raw-pointer singly-linked
// list (L-ptr second-shape corpus, writer leg). Discipline: `Node`
// is a two-field struct (`int val`, `Node *next`); the entry takes
// the head pointer and the new node — both caller-owned — and
// returns the new head (`nd` for the empty list). Both params
// carry `__restrict__` (two live pointers can always alias, so
// uniqueness is claimed in the text and corroborated by a
// `noalias` oracle verdict; the single-pointer exemption does not
// apply). The entry itself never allocates. The new node's link
// is normalized first (`nd->next = nullptr` — loud on a null
// `nd`); a null head returns the node; otherwise the loop chases
// `cur` while `cur->next != nullptr` and swings the tail link to
// the node. Null dereferences are loud. Cycles are out of scope
// (the contract assumes an acyclic chain; fuel bounds the chase
// as a backstop).
// Spec: on exit the `head`-rooted chain ends in `nd` with
// `nd->next == nullptr` and all payloads untouched; return is
// `head` (`nd` iff empty). The `nd`-rooted input chain is
// unconstrained (only its head link is overwritten).
struct Node {
  int val;
  Node *next;
};

Node *list_append(Node * __restrict__ head, Node * __restrict__ nd) {
  nd->next = nullptr;
  if (head == nullptr) {
    return nd;
  }
  Node *cur = head;
  while (cur->next != nullptr) {
    cur = cur->next;
  }
  cur->next = nd;
  return head;
}
