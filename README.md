# Splay Trees

This is an implementation of splay trees written in rust. This was mostly a
proof of concept work, and it ended up working out well!

This repo now has structure of a `rustpkg` repository, so it should be
installable via

```
rustpkg install github.com/alexcrichton/rs-splay
```

Still haven't quite figured out how to put it in an `extern mod` just yet...

This code is all released under the MIT license. The implementation of splaying
is largely based on ftp://ftp.cs.cmu.edu/usr/ftp/usr/sleator/splaying/top-down-splay.c
