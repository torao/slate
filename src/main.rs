use clap::{arg, Command};

fn main() {
  let matches = Command::new("Banded Hash Tree")
    .name(env!("CARGO_PKG_NAME"))
    .version(env!("CARGO_PKG_VERSION"))
    .author(env!("CARGO_PKG_AUTHORS"))
    .about(env!("CARGO_PKG_DESCRIPTION"))
    .arg(arg!(<DATABASE>).required(true).help("Database to be operated."))
    .arg(arg!(<COMMAND>).required(false).help("A command to be executed against the database."))
    .get_matches();
  let db = matches.get_one::<String>("DATABASE").unwrap();
  match matches.get_one::<String>("COMMAND") {
    Some(cmd) => println!("COMMAND: {}", cmd),
    None => println!("COMMAND: query"),
  }
  println!("DATABASE: {}", db);
}
