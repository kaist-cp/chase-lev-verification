#include <stdbool.h>
#include <stdatomic.h>

//@rc::import deque_def from refinedc.project.ex.deque
//@rc::context `{!dequeG Σ}

typedef struct
deque {
    int arr[16];
    int size;
    _Atomic int top;
    int bot;
} *deque_t;

//[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_weak_try_inc")]]
[[rc::parameters("g: gname", "q : loc", "n: nat", "v: Z")]]
[[rc::args("q @ &shr<deque<g>>", "v @ int<i32>")]]
[[rc::requires("[own_deque g n q]")]]
[[rc::atomic_parameters("l : {list Z}")]]
[[rc::atomic_requires("[deque_content g l]")]]
[[rc::atomic_ensures("[deque_content g (l++[v])]")]]
[[rc::ensures("shr q : deque<g>")]]
[[rc::ensures("[own_deque g n q]")]]
void push(deque_t q, int v) {
  int b = q->bot;
  int sz = q->size;
  if(q->top + sz <= b) push(q, v);
  else {
    q->arr[b % sz] = v;
    q->bot = b+1;
  }
}
