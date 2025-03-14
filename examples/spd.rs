use corundum::open_flags::*;
use std::time::Instant;

fn main() {
    use corundum::default::*;
    use std::env;

    type P = Allocator;

    struct Root {
        list: PVec<PCell<i32>>,
    }

    impl RootObj<P> for Root {
        fn init(j: &Journal) -> Self {
            let mut list = PVec::with_capacity(3000, j);
            for i in 0..3000 {
                list.push(PCell::new(i), j);
            }
            Self { list }
        }
    }
    use std::vec::Vec as StdVec;

    let args: StdVec<String> = env::args().collect();

    if args.len() < 2 {
        println!("usage: {} file-name", args[0]);
        return;
    }

    let root = P::open::<Root>(&args[1], O_CF).unwrap();

    for c in &[10, 100, 500, 1000, 2000, 3000] {
        let now = Instant::now();
        transaction(|j| {
            for i in 0..*c {
                root.list[i].set(root.list[(i + 1) % *c].get(), j);
            }
        })
        .unwrap();
        let t = now.elapsed().as_micros();
        println!("Transaction Size {:4}: {:>8} us", c, t);
    }
}
