
lazy val root = project
  .in(file("."))
  .aggregate(
    ProjectRef(file("dotty-parser-combinators"), "root"),
    ProjectRef(file("stalker"), "root")
  )

