#include <stdbool.h>
#include <stdatomic.h>

//@rc::import excl from iris.algebra
//@rc::import auth from iris.algebra
//@rc::import counter_def from refinedc.project.ex.counter
//@rc::context `{!counterG Σ}

typedef struct
counter {
    _Atomic int cnt;
} *counter_t;

[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_weak_try_inc")]]
[[rc::parameters("p : loc", "g: gname", "n: Z")]]
[[rc::args("p @ &own<counter<g>>")]]
[[rc::requires("{((n+1)%Z ≤ max_int i32)%Z}")]]
[[rc::requires("[own g (◯ (Excl' n))]")]]
[[rc::exists("b : bool", "m: Z")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : counter<g>")]]
[[rc::ensures("[own g (◯ (Excl' m))]")]]
[[rc::ensures("{if b then (m = n+1)%Z else (m = n)%Z}")]]
bool weak_try_inc(counter_t c) {
    int v = c->cnt;
    int v2 = v + 1;
    return atomic_compare_exchange_strong(&(c->cnt), &v, v2);
}

[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_weak_inc")]]
[[rc::parameters("p : loc", "g: gname", "n: Z")]]
[[rc::args("p @ &own<counter<g>>")]]
[[rc::requires("{((n+1)%Z ≤ max_int i32)%Z}")]]
[[rc::requires("[own g (◯ (Excl' n))]")]]
[[rc::ensures("own p : counter<g>")]]
[[rc::ensures("[own g (◯ (Excl' (n+1)%Z))]")]]
void weak_inc(counter_t c) {
    while(!weak_try_inc(c));
}

[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_try_inc")]]
[[rc::parameters("p : loc", "g : gname")]]
[[rc::atomic_parameters("n: Z")]]
[[rc::args("p @ &shr<counter<g>>")]]
[[rc::atomic_requires("{((n+1)%Z ≤ max_int i32)%Z}")]]
[[rc::atomic_requires("[own g (◯ (Excl' n))]")]]
[[rc::exists("b : bool", "m : Z")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("shr p : counter<g>")]]
[[rc::atomic_ensures("[own g (◯ (Excl' m))]")]]
[[rc::atomic_ensures("{if b then (m = n+1)%Z else (m = n)%Z}")]]
bool try_inc(counter_t c) {
    int v = c->cnt;
    int v2 = v + 1;
    return atomic_compare_exchange_strong(&(c->cnt), &v, v2);
}

[[rc::manual_proof("refinedc.project.ex.counter:counter_proof, type_inc")]]
[[rc::parameters("p : loc", "g : gname")]]
[[rc::atomic_parameters("n : Z")]]
[[rc::args("p @ &shr<counter<g>>")]]
[[rc::atomic_requires("{((n+1)%Z ≤ max_int i32)%Z}")]]
[[rc::atomic_requires("[own g (◯ (Excl' n))]")]]
[[rc::ensures("shr p : counter<g>")]]
[[rc::atomic_ensures("[own g (◯ (Excl' (n+1)%Z))]")]]
void inc(counter_t c) {
    while(!try_inc(c));
}
