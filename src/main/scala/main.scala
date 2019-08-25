import scala.io.Source

object FWS {

  def processCode(code : String) : Unit = {
    val parseResult : FWSParser.ParseResult[Ast] = FWSParser.parseAll(FWSParser.expr, code);
    val ast : Ast = parseResult.get;
    println("  parsed result: " + ast);
    val store = new EmptyStore{}
    val tyenv = new EmptyTypeEnv{}
    val res : Either[TypeError, Type] = FWSTypeChecker.typeCheck(store, tyenv, ast)
    res match {
      case Left(err) =>
        println("! type error: " + err)

      case Right(ty) =>
        println("  type: " + ty)
        val interp = new FWSInterpreter
        interp.run(ast)
    }
  }

  def main(args : Array[String]) : Unit =
    args.length match {
      case 2 =>
        try {
          val source = Source.fromFile(args(1))
          val code = source.mkString;
          source.close();
          processCode(code)
        } catch {
          case _ : java.io.FileNotFoundException =>
            println("! file '" + args(1) + "' not found")
        }

      case _ =>
        println("! wrong number of arguments; required one argument")
    }
}
