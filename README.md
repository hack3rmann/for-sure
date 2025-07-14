# The `Almost` type

Sometimes you need the optional type which is **almost** always is `Some`.
The `Almost` type provides such functionality. It implements both
`Deref<Target = T>` and `DerefMut` which panic if the value is uninitilized.

# Use cases

It is actually really bad to use `Almost` instead of `Option` because it
disables 'null-safety' of Rust. But in some use cases it may help a lot.
For example, structs with two-factor inititalization:

```rust
use for_sure::prelude::*;

// first init factor writes `Nil` to `window`
#[derive(Default)]
struct MyApp {
    window: Almost<Window>,
}

// trait implementation which initializes `MyApp`
impl App for MyApp {
    // this function calls always when `MyApp` is initialized,
    // but we forced to use option-like types
    fn open_window(&mut self, name: &str) {
        // the second factor initializes window completely
        self.window = Value(Window::new(name));
    }

    fn update(&mut self) {
        // you can access window's methods (or fields) without
        // writing `.as_ref().unwrap()` everywhere
        println!("name: {}", self.window.name());
    }
}
```

Note that it will panic if `Almost`'s value accessed uninitilized.

# Default features

- `std` - enables `std` library.
