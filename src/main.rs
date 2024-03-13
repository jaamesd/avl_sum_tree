#[allow(dead_code)]

extern crate rand;

fn main() {
    let rand = rand::random::<i32>();
    println!("{:?}", rand % -100);
    println!("{:?}", rand % 100);
}