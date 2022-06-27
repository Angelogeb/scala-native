# Local Scala Native

This is a fork of the [Scala Native compiler](https://github.com/scala-native/scala-native) (links below)
that implements variable sized stack-allocated values on a shadow stack as described in
_"What If We Don’t Pop the Stack? The Return of 2nd-Class Values"_.

## Directory structure
The `localplugin` directory contains the type plugin implementing
the type system.

Code generation required changes mainly in
* `nscplugin`: `scalac` phase implementing the Scala Native frontend that generates NIR files
* `nativelib`: GC code
* `nir`: native ir data structures. Added `localalloc` node + updates `arrayalloc` to include whether array is local

The `sandbox` directory contains example code and benchmarks.

The `coq` directory contains the mechanization of the theorems
in Coq.

## Running the benchmarks

### Building the image (option 1)
The project provides a `ImageDockerfile` to reproduce the development and
evaluation environment.

To build the image run
```
make image
```

The command above will create an image called `local-scala-native`.
You can check this by running `docker images`.

### Loading the available image (option 2)
Alternatively, if a pre-built image of this project was downloaded,
it is possible to import it as follows.

```
docker load -i local-scala-native.tar.gz
```

### Run commands

To run the benchmarks, first run the container interactively.
```
docker run --name ecoop_container --rm -it local-scala-native bash
```

Then, in the container shell just started run
```
./run.sh
```

This will produce two files under the `tables` directory:
- `tables/runtime.csv` corresponds to the table in Fig. 14
- `tables/gc_stats.csv` corresponds to Table 1

To modify and explore the repository inside the container we suggest
to use Visual Studio Code with the [Remote - Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
extension (also [described here](https://code.visualstudio.com/docs/remote/containers)).

It is possible to copy files from the container to host through
the `docker cp` command

```
docker cp ecoop_container:/home/local-scala-native/tables/gc_stats.csv .
```
### Storage mode walk-through

The `sandbox` directory/project contains the code of the benchmarks
and additionally a walk-through on storage modes (`Examples.scala`).

There are two main entries, one in `Benchmarks.scala` and one in `Examples.scala`.
`Benchmarks.scala` is the default main entry and it is possible to recompile it
with the following command.

```
sbt sandbox/nativeLink
```

This produces the binary `sandbox/target/scala-2.12/sandbox-out`.
The `sandbox/target/scala-2.12/native` directory contains the
native ir and llvm ir representations of the code.

To compile and run the code to use the main method in `Examples.scala`
run the following command.

```
sbt run-examples
```

This will produce a new binary at the same path with main entry the
one in `Examples.scala`.

If a mis-compilation arises due to a sequence of commands
it is possible to clean the artifacts with

```
sbt sandbox/clean
```

### Cleanup

To delete the image, ensure that the container is not running
by closing the interactive session and then run.

```
docker rmi local-scala-native
```
