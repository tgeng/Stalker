val dottyVersion = "0.24.0-RC1"

lazy val root = project
  .in(file("."))
  .settings(
    name := "stalker",
    version := "0.1.0",

    scalaVersion := dottyVersion,

    libraryDependencies ++= Seq(
      "io.github.tgeng" %% "dotty-parser-combinators" % "0.2.5",
      "org.scalatest" %% "scalatest" % "3.1.2" % "test",
    ),
    scalacOptions += "-Yexplicit-nulls",
    scalacOptions += "-Ykind-projector",
    scalacOptions += "-Ycheck-init"
  )
