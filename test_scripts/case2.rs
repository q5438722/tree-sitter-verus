
use vstd::prelude::*;

fn main() {}

verus! {
proof fn LogRangeMatchesQueue_append(
    queue: Seq<nat>,
    queueIndex: nat,
)
    requires
        0 <= queueIndex <= queue.len(),
    ensures
        0 <= queueIndex <= queue.len(),
{
    while(1 < 2)
    {}

    // Trivially false if it doesn NOT match
    // Otherwise finish:
    assert(new_log.contains_key(logIndexUpper)) by (nonlinear_arith)
        requires
            0 <= logIndexUpper < logIndexUpper + 1,
    {}

    assert(new_log.contains_key(logIndexUpper)) by (nonlinear_arith)
        requires
            0 <= logIndexUpper < logIndexUpper + 1,
    {};;;

    assert(new_log.contains_key(logIndexUpper)) by 
    {
        wow();
        if (a < b) {
            say();
        }
        else {d = e + f;}
    }


    admit();
}
}
