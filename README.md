# lockfree
Lockfree priority queue implementation. In its current state, it's just a linked list with priority-based push and pop. Performance is thus likely to be miserable. The idea is to integrate skip-lists, which should leave us with something reasonable.