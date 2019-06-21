
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
case class CannotLookupSingletonType(p : Path)        extends EvalError


class FWSInterpreter {


  trait MapPair {

    type ValueMap = Map[String, ValueDeclBody]
    type TypeMap  = Map[String, TypeDeclBody]

    val body : (ValueMap, TypeMap)


    def getValue(vlabel : String) : Option[ValueDeclBody] =
      body match { case (valmap, _) => valmap.get(vlabel) }


    def getType(tlabel : String) : Option[TypeDeclBody] =
      body match { case (_, tymap) => tymap.get(tlabel) }


    def mergeByRightHandSidePriority[K, V](map1 : Map[K, V], map2 : Map[K, V]) : Map[K, V] =
      map2.foldLeft(map1){ case (map, (k, v)) =>
        map + ((k, v))
      }


    def concat(mapPair2 : MapPair) : MapPair =
      (body, mapPair2.body) match { case ((valmap1, tymap1), (valmap2, tymap2)) =>
        val valmap = mergeByRightHandSidePriority(valmap1, valmap2);
        val tymap = mergeByRightHandSidePriority(tymap1, tymap2);
        new MapPair { val body = (valmap, tymap) }
      }
  }

  class EmptyMapPair extends MapPair {
    val body = (Map(), Map())
  }

  class MapPairOfDeclarations(decls : List[Declaration]) extends MapPair {
    val body = {
      val init : (ValueMap, TypeMap) = (Map(), Map());
      decls.foldLeft(init){ case ((valmap, tymap), decl) =>
        decl match {
          case DeclForValueLabel(vl, vd) => (valmap + ((vl, vd)), tymap)
          case DeclForTypeLabel(tl, td)  => (valmap, tymap + ((tl, td)))
        }
      }
    }
  }


  trait Env {

    val body : Map[String, MapPair]


    def add(x : String, mapPair : MapPair) : Env = {
      new Env { val body = Env.this.body + ((x, mapPair)) }
    }


    def findValueDecl(x : String, vlabel : String) : Option[ValueDeclBody] =
      body.get(x) flatMap { mapPair =>
        mapPair.getValue(vlabel)
      }


    def findTypeDecl(x : String, tlabel : String) : Option[TypeDeclBody] =
      body.get(x) flatMap { case mapPair =>
        mapPair.getType(tlabel)
      }

  }

  class EmptyEnv extends Env {
    val body = Map()
  }


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
        interpretType(env, ty) flatMap { tyval =>
          lookupDeclarations(env, tyval, x) flatMap { mapPair =>
            interpretAst(env.add(x, mapPair), ast0)
          }
        }

      case Var(x) =>
        Right(ValVar(x))

      case Access(ast0, vlabel) =>
        interpretAst(env, ast0) flatMap { case ValVar(x) =>
          env.findValueDecl(x, vlabel) match {
            case None                               => Left(ValueLabelNotFound(vlabel))
            case Some(DeclDef(_, _, _, _))          => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclVal(_, _, None))          => Left(FieldNotEmbodied(vlabel))
            case Some(DeclVal(_, ty, Some(astNew))) => interpretAst(env, astNew)
          }
        }

      case Call(ast0, vlabel, astargs) =>
        interpretAst(env, ast0) flatMap { case ValVar(x) =>
          (env.findValueDecl(x, vlabel) match {
            case None                                       => Left(ValueLabelNotFound(vlabel))
            case Some(DeclVal(_, _, _))                     => Left(NotAFieldButAMethod(vlabel))
            case Some(DeclDef(_, _, _, None))               => Left(MethodNotImplemented(vlabel))
            case Some(DeclDef(_, params, ty, Some(astImp))) => Right((params, ty, astImp))
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
    }


  val astOfPath : Path => Ast =
    path => {
      path match { case Path(x, vlabels) =>
        vlabels.foldLeft(Var(x) : Ast){ (astacc, vlabel) =>
          Access(astacc, vlabel)
        }
      }
    }


  def interpretType(env : Env, ty : Type) : Either[EvalError, TypeValue] =
    ty match {
      case TypeSelection(path, tlabel) =>
        val ast = astOfPath(path);
        interpretAst(env, ast) flatMap { case ValVar(x) =>
          Right(ValTypeSelection(x, tlabel))
        }

      case SingletonType(path) =>
        Right(ValSingletonType(path))

      case TypeSignature(tysig) =>
        interpretIntersection(env, tysig) flatMap { case tyvalsig =>
          Right(ValTypeSignature(tyvalsig))
        }
    }


  def interpretIntersection(env : Env, tysig : Intersection[Type]) : Either[EvalError, Intersection[TypeValue]] =
    tysig match { case Intersection(tys, x, decls) =>
        val resInit : Either[EvalError, List[TypeValue]] = Right(Nil);
        tys.foldLeft(resInit){ case (accres, ty) =>
          accres flatMap { tyvalacc =>
            interpretType(env, ty) flatMap { tyval =>
              Right(tyval :: tyvalacc)
            }
          }
        } flatMap { case tyvalsrev =>
          val tyvals = tyvalsrev.reverse;
          Right(Intersection(tyvals, x, decls))
        }
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
            substituteAst(varg, x, astImp)
          }
        };
        Right(astImpNew)
      }
    }


  val substituteAst : (Value, String, Ast) => Ast =
    (value, x, ast) => {
      val iter = substituteAst(value, x, _);
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


  def lookupDeclarations(env : Env, tyval : TypeValue, x : String) : Either[EvalError, MapPair] =
    tyval match {
      case ValTypeSelection(x, tlabel) =>
        env.findTypeDecl(x, tlabel) match {
          case None                    => Left(TypeLabelNotFound(tlabel))
          case Some(DeclType(_, None)) => Left(TypeNotEmbodied(tlabel))

          case Some(DeclType(_, Some(ty0))) =>
            interpretType(env, ty0) flatMap { tyval0 =>
              lookupDeclarations(env, tyval0, x)
            }

          case Some(DeclTrait(_, tysig)) =>
            interpretIntersection(env, tysig) flatMap { tyvalsig =>
              lookupDeclarations(env, ValTypeSignature(tyvalsig), x)
            }
        }

      case ValTypeSignature(Intersection(tyvals, phi, decls0)) => {
        val mapPairInit : MapPair = new EmptyMapPair;
        val resInit : Either[EvalError, MapPair] = Right(mapPairInit);
        tyvals.foldLeft(resInit){ (res, tyval) =>
          res flatMap { case mapPairAcc =>
            lookupDeclarations(env, tyval, x) flatMap { case mapPair =>
              Right((mapPairAcc.concat(mapPair)))
            }
          }
        } flatMap { case mapPairAcc =>
          val mapPair0 = new MapPairOfDeclarations(decls0);
          Right(mapPairAcc.concat(mapPair0))
        }
      }


      case ValSingletonType(p) =>
        Left(CannotLookupSingletonType(p))

    }
}
