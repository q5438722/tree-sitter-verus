use vstd::prelude::*;

fn main() {}

verus!{

#[verifier::loop_isolation(false)]
fn func(a: u64, b: u64, h: u64) -> (result: u64)
    requires
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= h <= 100,
        h % 2 == 0,
    ensures
        result == (a + b) * h / 2,
{
    while temp_sum >= 2
        invariant
            temp_sum >= 0,
            temp_sum + 2 * i == sum,
            result == i,
            1 <= a <= 100,
            1 <= b <= 100,
            1 <= h <= 100,
            h % 2 == 0,
        decreases temp_sum,
    {
        temp_sum -= 2;
        result += 1;
        i += 1;
    }
    return result;
}
}