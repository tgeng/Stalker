val dottyVersion = "0.24.0-RC1"

lazy val root = project
  .in(file("."))
  .dependsOn(
    ProjectRef(file("../dotty-parser-combinators"), "root")
  )
  .settings(
    name := "stalker",
    version := "0.1.0",

    scalaVersion := dottyVersion,

    libraryDependencies ++= Seq(
      // "org.scalactic" %% "scalactic" % "3.1.1",
      // "org.scalatest" %% "scalatest" % "3.1.1" % "test",
      // ("org.scalatestplus" %% "scalacheck-1-14" % "3.1.1.1" % "test")
        // .intransitive()
        // .withDottyCompat(scalaVersion.value),
      // ("org.scalacheck" %% "scalacheck" % "1.14.3" % "test")
      // .withDottyCompat(scalaVersion.value)
    ),
    scalacOptions += "-Yexplicit-nulls",
    scalacOptions += "-Ykind-projector",
    scalacOptions += "-Ycheck-init"
  )

