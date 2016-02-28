name := "scala-fp-scheme"

lazy val commonSettings = Seq(
  organization := "cats",
  version := "0.1.0",
  scalaVersion := "2.11.7",
  scalacOptions ++= Seq(
    "-deprecation",
    "-encoding", "UTF-8",
    "-feature",
    "-language:_"
  ),
  libraryDependencies ++=
    Seq("org.scala-lang" % "scala-compiler" % "2.11.7",
      "org.typelevel" %% "cats" % "0.4.1",
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
      "org.scalatest" % "scalatest_2.11" % "2.2.4" % "test"))

lazy val core = (project in file("."))
  .settings(commonSettings: _*)

