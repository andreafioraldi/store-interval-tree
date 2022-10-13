# store-interval-tree

A balanced unbounded interval-tree in Rust with associated values in the nodes.

Based on [rudac](https://crates.io/crates/rudac) and [bio](https://crates.io/crates/bio).

## Example

```rust
use store_interval_tree::IntervalTree;
use store_interval_tree::Interval;
use std::ops::Bound::*;

let mut interval_tree = IntervalTree::<usize, bool>::new();

interval_tree.insert(Interval::new(Excluded(0), Included(1)), true);
interval_tree.insert(Interval::new(Included(0), Excluded(3)), true);
interval_tree.insert(Interval::new(Included(6), Included(10)), true);
interval_tree.insert(Interval::new(Excluded(8), Included(9)), true);
interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), true);
interval_tree.insert(Interval::new(Included(16), Excluded(21)), true);
interval_tree.insert(Interval::new(Included(17), Excluded(19)), true);
interval_tree.insert(Interval::new(Excluded(19), Included(20)), true);
interval_tree.insert(Interval::new(Excluded(25), Included(30)), true);
interval_tree.insert(Interval::new(Included(26), Included(26)), true);

let interval = Interval::new(Included(8), Included(26));
let iter = interval_tree.query_mut(&interval);

for mut entry in iter {
    *entry.value() = false;
}
```
