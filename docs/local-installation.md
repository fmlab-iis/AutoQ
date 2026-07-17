# Local installation and build notes

These are the steps verified in the current environment to install dependencies, build AutoQ, and run the unit tests.

## 1) Install dependencies
Run the helper script from the repository root:

```bash
./install-dependencies.sh
```

This installs the required system packages (g++, make, cmake, Boost, ANTLR4) and creates the `build/` directory if it does not exist.

## 2) Build the project
Invoke the default release build target:

```bash
make
```

CMake will configure the project and then compile targets, producing the `build/cli/autoq` executable and required libraries. You may see a warning about missing Doxygen if it is not installed; this does not prevent the build.

## 3) Run tests
Execute the CTest suite from the repository root:

```bash
make test
```

The available unit test (`explicit_tree_aut_test`) should pass; in this run it completed in about a minute.

## 4) Run the CLI
After a successful build, the CLI binary is available at:

```bash
./build/cli/autoq
```

Use the `--help` flag to view available subcommands and options.
