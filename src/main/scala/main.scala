
object FWS {
  def main(args : Array[String]) : Unit =
    args.length match {
      case 2 =>
        val code = args(1);
        val ast = FWSParser.parseAll(FWSParser.expr, code);
        println(ast)

      case _ =>
        println("wrong number of arguments; required one argument")
    }
}
