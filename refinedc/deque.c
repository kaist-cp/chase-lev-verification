#include <stdbool.h>
#include <stdatomic.h>

// TODO import stuff here

typedef struct
deque {
    int arr[16];
    int size;
    _Atomic int top;
    int bot;
    _Atomic int cnt;
} *deque_t;

//[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_weak_try_inc")]]
[[rc::parameters("g: gname", "q : loc", "n: Z")]]
[[rc::args("q @ &shr<deque<g>>", "n @ int<i32>")]]
[[rc::requires("[is_deque g sz q]")]]
[[rc::requires("[own_deque g sz q]")]]
[[rc::atomic_parameters("l : {list Z}")]]
[[rc::atomic_requires("[deque_content g l]")]]
[[rc::atomic_ensures("[deque_content g (l++[n])]")]]
[[rc::ensures("shr q : deque<g>")]]
[[rc::ensures("[own_deque g sz q]")]]
void push(deque_t q, int n) {
  int b = q->bot;
  int sz = q->size;
  if(q->top + sz <= b) push(q, n);
  else {
    q->arr[b % sz] = n;
    q->bot = b+1;
  }
}

