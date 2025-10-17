fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut i: usize = usize::MAX;
    if args.len() > 1 {
        i = args[1].parse().unwrap_or(usize::MAX);
    }
    stuff::run_instances(i);
}
