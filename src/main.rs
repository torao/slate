use clap;

fn main() {
  let matches = clap::App::new("Logarithmic Multi-Tier Hash Tree")
    .version("1.0.0")
    .author("TAKAMI Torao <koiroha@gmail.com>")
    .arg(
      clap::Arg::with_name("DATABASE")
        .required(true)
        .help("database")
    )
    .get_matches();
  if let Some(db) = matches.value_of("DATABASE") {
    println!("DATABASE: {}", db);
  }
}
