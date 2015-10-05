# Splay Trees

[![Build Status](https://travis-ci.org/alexcrichton/splay-rs.svg?branch=master)](https://travis-ci.org/alexcrichton/splay-rs)

[Documentation](http://alexcrichton.com/splay-rs/splay/index.html)

This is an implementation of splay trees written in Rust. This was mostly a
proof of concept work, and it ended up working out well!

This repo is provided as a Cargo package, simply adjust your `Cargo.toml` to
include

```toml
[dependencies]
splay = "0.1"
```

This code is all released under the MIT license. The implementation of splaying
is largely based on
ftp://ftp.cs.cmu.edu/usr/ftp/usr/sleator/splaying/top-down-splay.c
