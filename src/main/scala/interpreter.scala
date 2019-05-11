

trait Env {

  type ValueMap = Map[String, ValueDeclBody]
  type TypeMap  = Map[String, TypeDeclBody]

  val body : Map[String, (ValueMap, TypeMap)]

  def +(x : String, decls : List[Declaration]) = {
    val mapPair : (ValueMap, TypeMap) = {
      val init : (ValueMap, TypeMap) = (Map(), Map());
      decls.foldLeft(init){ case ((valmap, tymap), decl) =>
        decl match {
          case DeclForValueLabel(vl, vd) => (valmap + ((vl, vd)), tymap)
          case DeclForTypeLabel(tl, td)  => (valmap, tymap + ((tl, td)))
        }
      }
    };
    new Env { val body = Env.this.body + ((x, mapPair)) }
  }


  def findValueDecl(x : String, vlabel : String) : Option[ValueDeclBody] =
    body.get(x) flatMap { case (valmap, _) =>
      valmap.get(vlabel)
    }


  def findTypeDecl(x : String, tlabel : String) : Option[TypeDeclBody] =
    body.get(x) flatMap { case (_, tymap) =>
      tymap.get(tlabel)
    }

}

class EmptyEnv extends Env {
  val body : Map[String, (ValueMap, TypeMap)] = Map()
}


sealed trait EvalError
case class NotImplementedYet(msg : String)            extends EvalError
case class ValueLabelNotFound(vl : String)            extends EvalError
case class TypeLabelNotFound(tl : String)             extends EvalError
case class FieldNotEmbodied(vl : String)              extends EvalError
case class MethodNotImplemented(vl : String)          extends EvalError
case class TypeNotEmbodied(tl : String)               extends EvalError
case class NotAFieldButAMethod(vl : String)           extends EvalError
case class NotAMethodButAField(vl : String)           extends EvalError
case class WrongNumberOfArguments(le : Int, la : Int) extends EvalError

class FWSInterpreter {

  def run(ast : Ast) : Unit = {
    val env = new EmptyEnv;
    interpretAst(env, ast) match {
      case Right(v) =>
        println("returned value: " + v)

      case Left(e) =>
        println("error: " + e)
    }
  }


  def interpretAst(env : Env, ast : Ast) : Either[EvalError, Value] =
    ast match {
      case ValNewIn(x, ty, ast0) =>
        lookupDeclarations(env, ty, x) flatMap { case decls =>
          interpretAst(env + (x, decls), ast0)
        }

      case Var(x) =>
        Right(ValVar(x))

      case Access(ast0, vlabel) =>
        interpretAst(env, ast0) flatMap { case ValVar(x) =>
          env.findValueDecl(x, vlabel) match {
            case None                            => Left(ValueLabelNotFound(vlabel))
            case Some(DeclDef(_, _, _))          => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclVal(_, None))          => Left(FieldNotEmbodied(vlabel))
            case Some(DeclVal(ty, Some(astNew))) => interpretAst(env, astNew)
          }
        }

      case Call(ast0, vlabel, astargs) =>
        interpretAst(env, ast0) flatMap { case ValVar(x) =>
          (env.findValueDecl(x, vlabel) match {
            case None                                    => Left(ValueLabelNotFound(vlabel))
            case Some(DeclVal(_, _))                     => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclDef(_, _, None))               => Left(MethodNotImplemented(vlabel))
            case Some(DeclDef(params, ty, Some(astImp))) => Right((params, ty, astImp))
          }) flatMap { case (params, ty, astImp) =>
            val resInit : Either[EvalError, List[Value]] = Right(Nil);
            astargs.foldLeft(resInit){ case (res, astarg) =>
              res flatMap { case vacc =>
                interpretAst(env, astarg) flatMap { case varg =>
                  Right(varg :: vacc)
                }
              }
            } flatMap { case vargsrev : List[Value] =>
              val vargs = vargsrev.reverse;
              substituteParams(vargs, params, astImp) flatMap { case astNew =>
                interpretAst(env, astNew)
              }
            }
          }
        }
/*
        Left(NotImplementedYet("evaluation for method calls"))  // TEMPORARY
*/
    }


  val substituteParams : (List[Value], List[(String, Type)], Ast) => Either[EvalError, Ast] =
    (vargs, params, astImp) => {
      val lenActual = vargs.length;
      val lenExpected = params.length;
      if (lenActual != lenExpected) {
        Left(WrongNumberOfArguments(lenExpected, lenActual))
      } else {
        val lst : List[(Value, (String, Type))] = vargs.zip(params);
        val astImpNew : Ast = {
          lst.foldLeft(astImp){ case (astImp, (varg, (x, _))) =>
            substitute(varg, x, astImp)
          }
        };
        Right(astImpNew)
      }
    }


  val substitute : (Value, String, Ast) => Ast =
    (value, x, ast) => {
      val iter = substitute(value, x, _);
      ast match {
        case ValNewIn(y, ty, ast0) =>
          if (y == x) { ast } else {
            ValNewIn(y, ty, iter(ast0))
          }

        case Var(y) =>
          if (y == x) { Var(x) } else { ast }

        case Access(ast0, vlabel) =>
          Access(iter(ast0), vlabel)

        case Call(ast0, vlabel, astargs) =>
          Call(iter(ast0), vlabel, astargs.map(iter))
      }
    }


  def lookupDeclarations(env : Env, ty : Type, x : String) : Either[EvalError, List[Declaration]] =
    // FIXME; should apply to "type values", not to types
    ty match {
      case TypeSelection(Path(x, _), tlabel) =>
        env.findTypeDecl(x, tlabel) match {
          case None                      => Left(TypeLabelNotFound(tlabel))
          case Some(DeclType(None))      => Left(TypeNotEmbodied(tlabel))
          case Some(DeclType(Some(ty0))) => lookupDeclarations(env, ty0, x)
          case Some(DeclTrait(tysig))    => lookupDeclarations(env, TypeSignature(tysig), x)
        }

      case TypeSignature(tysig) =>
        Right(Nil)  // TEMPORARY

      case SingletonType(p) =>
        Right(Nil)  // TEMPORARY

    }
}
