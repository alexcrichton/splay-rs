# Splay Trees

This is an implementation of splay trees written in Rust. This was mostly a
proof of concept work, and it ended up working out well!

This repo is provided as a Cargo package, simply adjust your `Cargo.toml` to include

```
[dependencies.splay]
git = "https://github.com/alexcrichton/rs-splay"
```

This code is all released under the MIT license. The implementation of splaying
is largely based on ftp://ftp.cs.cmu.edu/usr/ftp/usr/sleator/splaying/top-down-splay.c
