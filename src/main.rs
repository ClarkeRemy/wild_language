//! this is main

mod tokenize;


fn main() {


let g = vec![3, 2,3 ,4,545,56,665436,6,6,3,63,5];

match g.as_slice() {
  h @ [3,2,3, j@..,63,5] => println!("{j:?}"),
  _=> ()
}



}
