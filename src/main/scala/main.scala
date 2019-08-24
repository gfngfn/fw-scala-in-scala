
object FWS {
  def main(args : Array[String]) : Unit =
    args.length match {
      case 2 =>
        val code = args(1);
        val parseResult : FWSParser.ParseResult[Ast] = FWSParser.parseAll(FWSParser.expr, code);
        val ast : Ast = parseResult.get;
        println("parsed result: " + ast);
        val store = new EmptyStore{}
        val tyenv = new EmptyTypeEnv{}
        val res : Either[TypeError, Type] = FWSTypeChecker.typeCheck(store, tyenv, ast)
        res match {
          case Left(err) =>
            println("type error: " + err)

          case Right(ty) =>
            println("type: " + ty)
            val interp = new FWSInterpreter
            interp.run(ast)
        }

      case _ =>
        println("wrong number of arguments; required one argument")
    }
}
