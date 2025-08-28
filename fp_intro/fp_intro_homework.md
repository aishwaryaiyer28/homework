# Homework


Install the following software

1. Visual Studio Code
2. Java SDK version 11+

Install the following Extensions for Visual Studio Code

1. Scala (Metals)
2. Scala Syntax (official)


Try to compile and run the hello world project with Visual Studio Code.

In VSC, you should see the `Terminal` open with a sbt session running.

```
[info] started sbt server
sbt:helloworld> 
```

Then type `compile` to build and `run` to run the `main` method in the `Main` class/object
```
sbt:helloworld> compile
[success] Total time: 1 s, completed Jun 28, 2022, 8:31:44 PM
sbt:helloworld> run
[info] running com.github.helloworld.Main 
hello world
[success] Total time: 0 s, completed Jun 28, 2022, 8:31:47 PM
sbt:helloworld> 
```

Lastly, type `test` to run the test cases found in `src/test`

```
sbt:helloworld> test
[info] compiling 1 Scala source to /home/luzm/git/compilerdesgin/homework/fp_intro/target/scala-3.1.2/test-classes ...
[info] TestMain:
[info] - test1
[info] Run completed in 186 milliseconds.
[info] Total number of tests run: 1
[info] Suites: completed 1, aborted 0
[info] Tests: succeeded 1, failed 0, canceled 0, ignored 0, pending 0
[info] All tests passed.
[success] Total time: 4 s, completed Jun 30, 2022, 1:39:50 PM
sbt:helloworld> 
```