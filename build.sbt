// build.sbt
scalaVersion := "2.12.8"

scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked", "-Xlint")
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
