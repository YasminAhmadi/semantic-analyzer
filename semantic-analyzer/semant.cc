#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <set>
#include <sstream>

extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;

static void initialize_constants(void) {
  arg = idtable.add_string("arg");
  arg2 = idtable.add_string("arg2");
  Bool = idtable.add_string("Bool");
  concat = idtable.add_string("concat");
  cool_abort = idtable.add_string("abort");
  copy = idtable.add_string("copy");
  Int = idtable.add_string("Int");
  in_int = idtable.add_string("in_int");
  in_string = idtable.add_string("in_string");
  IO = idtable.add_string("IO");
  length = idtable.add_string("length");
  Main = idtable.add_string("Main");
  main_meth = idtable.add_string("main");
  //   _no_class is a symbol that can't be the name of any
  //   user-defined class.
  No_class = idtable.add_string("_no_class");
  No_type = idtable.add_string("_no_type");
  Object = idtable.add_string("Object");
  out_int = idtable.add_string("out_int");
  out_string = idtable.add_string("out_string");
  prim_slot = idtable.add_string("_prim_slot");
  self = idtable.add_string("self");
  SELF_TYPE = idtable.add_string("SELF_TYPE");
  Str = idtable.add_string("String");
  str_field = idtable.add_string("_str_field");
  substr = idtable.add_string("substr");
  type_name = idtable.add_string("type_name");
  val = idtable.add_string("_val");
}

static Class_ curclass = NULL;
static ClassTable *classtable;
// ObjectId to Class(Type)
static SymbolTable<Symbol, Symbol> objectEnv;
// methods map along inheritance path
static SymbolTable<Symbol, Feature_class> inheritEnv;
// ClassName to methodName to methods
static std::map<Symbol, SymbolTable<Symbol, Feature_class> > methodEnv;

ClassTable::ClassTable(Classes classes) : semant_errors(0), error_stream(cerr) {
    
  //no matter what classes are defined in the program,
  //the basic cool classes are always defined
  install_basic_classes();
  //visit, e(error) and c(cycle) will be used to check for cycles
  //in inheritance graph
  std::map<Class_, int> visit;
  bool e = false;
  bool c = false;
    
  //iterating over classes
  for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
    curclass = classes->nth(i);
    Symbol curname = curclass->get_name();
    //checking if the class is already defined
    if (classmap.find(curname) != classmap.end()) {
      semant_error(curclass)<< "Error: Class "<<curname<< " is already defined.\n";
      return;
    }
    //checking if the class defined is a basic class
    if (curname == Str || curname == Int || curname == Bool || curname == SELF_TYPE || curname == IO ||  curname == Object) {
      semant_error(curclass)
          << "Error: Redefinition of basic class: "<<curname<< std::endl;
      return;
    }

    classmap.insert(std::make_pair(curname, curclass));
    ingraph[curclass->get_parent()].push_back(curname);
    visit.insert(std::make_pair(curclass, 0));
  }
  //again we iterate over classes, for each class we go through
  //all its ancestors checking if there is a cycle or some ancestor has
  //more than on child (which is not allowed in the COOL language)
  for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
    curclass = classes->nth(i);
    if (visit[curclass] == 0) {
    //if this class is not checked yet :
      incyc(curclass, classes, visit, e, c);
      if (e)
        return;
    }
  }
  //one of the classes has to be Main
  if (classmap.find(Main) == classmap.end()) {
      semant_error()<< "Error: Main is not defined.\n";
      return;
  }
    
}

//Checking if the graph is well-formed

void ClassTable::incyc(Class_ Current, Classes classes, std::map<Class_, int> &visit,
                     bool &e, bool &c) {

  //we're only checking for unvisited classes (==>with their visit == 0)
  //therefore if it is 1, it means we're at second or more iteration and
  //current is one of the ancestors of the initial class
  //There are two cases which result in an ancestor be visited
  // First reason : this ancestor was an earlier ancestor too, meaning
  //it is the current ancestor's child (not an immediate child necessarily)
  //which is a cycle ==> ERROR
  // Second reason : this ancestor was an ancestor to another class in previous
  //function calls, therefore it has more than one child ( if it is reachable
  //by multiple branches) ==> multiple inheritance, which is not allowed in COOl
  // ==> ERROR

  if (visit[Current] == 1) {
    semant_error(Current) << "Fatal Error: Inheritance cycle or multiple inheritance. \n" ;
    c = true;
    e = true;
    return;
  }
  //The class you're inheritting from must be defined in the program
  Symbol Parent = Current->get_parent();
  if (classmap.find(Parent) == classmap.end()) {
    semant_error(Current) << "Error: Class " << Current->get_name()
                      << "is inheritting from an undefined class: \"" <<Parent<< std::endl;
    e = true;
    return;
  }
  //Class can't inherit from Str, Int, Bool or Self_Type
  if (Parent == Str || Parent == Int || Parent == Bool || Parent == SELF_TYPE) {
    semant_error(Current) << "Error: Class " << Current->get_name()
                      << " inherits from class: " << Parent << std::endl;
    e = true;
    return;
  }
  //this class is now visited
  visit[Current] = 1;
  //if parent is object we're at root and no more ancestors to check
  if (Parent != Object)
    incyc(classmap[Parent], classes, visit, e, c);
  //since cycles involve more than one class, we print them all here
  if (c) {
    semant_error(Current)<< "Cyclic inheritance involving class \"" << Current->get_name()<< "\" .\n";
  }
  if (e)
    return;
}

void ClassTable::install_basic_classes() {

  // The tree package uses these globals to annotate the classes built below.
  // curr_lineno  = 0;
  Symbol filename = stringtable.add_string("<basic class>");

  // The following demonstrates how to create dummy parse trees to
  // refer to basic Cool classes.  There's no need for method
  // bodies -- these are already built into the runtime system.

  // IMPORTANT: The results of the following expressions are
  // stored in local variables.  You will want to do something
  // with those variables at the end of this method to make this
  // code meaningful.

  //
  // The Object class has no parent class. Its methods are
  //        abort() : Object    aborts the program
  //        type_name() : Str   returns a string representation of class name
  //        copy() : SELF_TYPE  returns a copy of the object
  //
  // There is no need for method bodies in the basic classes---these
  // are already built in to the runtime system.

  Class_ Object_class = class_(
      Object, No_class,
      append_Features(
          append_Features(single_Features(method(cool_abort, nil_Formals(),
                                                 Object, no_expr())),
                          single_Features(method(type_name, nil_Formals(), Str,
                                                 no_expr()))),
          single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
      filename);

  //
  // The IO class inherits from Object. Its methods are
  //        out_string(Str) : SELF_TYPE       writes a string to the output
  //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
  //        in_string() : Str                 reads a string from the input
  //        in_int() : Int                      "   an int     "  "     "
  //
  Class_ IO_class = class_(
      IO, Object,
      append_Features(
          append_Features(
              append_Features(single_Features(method(
                                  out_string, single_Formals(formal(arg, Str)),
                                  SELF_TYPE, no_expr())),
                              single_Features(method(
                                  out_int, single_Formals(formal(arg, Int)),
                                  SELF_TYPE, no_expr()))),
              single_Features(
                  method(in_string, nil_Formals(), Str, no_expr()))),
          single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
      filename);

  //
  // The Int class has no methods and only a single attribute, the
  // "val" for the integer.
  //
  Class_ Int_class = class_(
      Int, Object, single_Features(attr(val, prim_slot, no_expr())), filename);

  //
  // Bool also has only the "val" slot.
  //
  Class_ Bool_class = class_(
      Bool, Object, single_Features(attr(val, prim_slot, no_expr())), filename);

  //
  // The class Str has a number of slots and operations:
  //       val                                  the length of the string
  //       str_field                            the string itself
  //       length() : Int                       returns length of the string
  //       concat(arg: Str) : Str               performs string concatenation
  //       substr(arg: Int, arg2: Int): Str     substring selection
  //
  Class_ Str_class = class_(
      Str, Object,
      append_Features(
          append_Features(
              append_Features(
                  append_Features(
                      single_Features(attr(val, Int, no_expr())),
                      single_Features(attr(str_field, prim_slot, no_expr()))),
                  single_Features(
                      method(length, nil_Formals(), Int, no_expr()))),
              single_Features(method(concat, single_Formals(formal(arg, Str)),
                                     Str, no_expr()))),
          single_Features(
              method(substr,
                     append_Formals(single_Formals(formal(arg, Int)),
                                    single_Formals(formal(arg2, Int))),
                     Str, no_expr()))),
      filename);
  //just like classes defined in the program these classes have to be
  //added to classmap
  classmap.insert(std::make_pair(Str, Str_class));
  classmap.insert(std::make_pair(Int, Int_class));
  classmap.insert(std::make_pair(Bool, Bool_class));
  classmap.insert(std::make_pair(Object, Object_class));
  classmap.insert(std::make_pair(IO, IO_class));

  //just like classes defined in the program for these classes
  //the inheritance graph has to be updated
  //class 'Object', inherites from no class
  ingraph[No_class].push_back(Object);
  //all other basic classes inherit from 'Object'
  ingraph[Object].push_back(Str);
  ingraph[Object].push_back(Int);
  ingraph[Object].push_back(Bool);
  ingraph[Object].push_back(IO);
}

//Finds the common ancestor of classes a1 and a2
Symbol ClassTable::CommonAncestor(Symbol a1, Symbol a2) {
  if (a1 == SELF_TYPE)
    a1= curclass->get_name();
  if (a2 == SELF_TYPE)
    a2= curclass->get_name();
    
  std::map<Symbol, bool> visit;
  std::map<Symbol, Class_>::iterator iter;
  //initially we want no class to be visited
  for (iter = classmap.begin(); iter != classmap.end(); ++iter) {
    visit.insert(std::make_pair(iter->first, false));
  }
  //p is the path from the given class to root (marking all its ancestors)
  Symbol p= a1;
  //we mark all the classes from a1 to the root (object) as visited
  while (p != Object) {
    visit[p] = true;
    p= classmap[p]->get_parent();
  }
  visit[p] = true;

  p= a2;
  //now we do the same for a2, but whenever an ancestor is already visited,
  //we crossed the path of all a1's ancestors==> this ancestor is a commmon ancestor
  while (visit[p] == false) {
    p= classmap[p]->get_parent();
  }
  return p;
}

bool ClassTable::isSubtype(Symbol child, Symbol ancestor) {
  //if both ancestor and child --> Self Type --> same dynamic type ==> is subtype
  if (child == SELF_TYPE && ancestor == SELF_TYPE)
    return true;
  //if father --> Self Type ==> can't type check
  //Even if type of child < = type of the class (C) --> ancestor's dynamic
  //type could be a subclass of C --> might not be an ancestor of A
  if (ancestor == SELF_TYPE)
    return false;
  //if child --> Self Type --> we have to check if it is subtype of the ancestor
  //or not
  if (child == SELF_TYPE)
    child = curclass->get_name();
  //by going through all the child's ancestors all the way to the root
  //if any of these ancestors is the ancestor ==> is subtype
  while (child != ancestor && child != No_class) {
    child = classmap[child]->get_parent();
  }
  if (child == ancestor)
    return true;
  //if the loop ended because of the second condition --> none of the ancestors is
  //the ancestor ==> is not subtype
  return false;
}
//this function returns the class the method belongs to
//the method either belongs to the class or one of its ancestors
Symbol ClassTable::findMethodInAncestor(Symbol classname, Symbol methodname) {
  if (classname == SELF_TYPE)
    classname = curclass->get_name();
  //no_class has no ancestor so we return it
  if (classname == No_class)
    return No_class;
  //if we find the method in its method environment then return
  if (methodEnv[classname].lookup(methodname) != NULL)
    return classname;
  //otherwise we go up until some ancestor is find which this method is found in
  //its method environment or we reach no_class
  return findMethodInAncestor(classmap[classname]->get_parent(), methodname);
}
  //returns true if class is not made up
  bool ClassTable::isBasic(Symbol a) {
    if (a != Int && a != Str && a != IO && a != Bool && a != Object)
      return false;
  return true;
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream &ClassTable::semant_error(Class_ c) {
  return semant_error(c->get_filename(), c);
}

ostream &ClassTable::semant_error(Symbol filename, tree_node *t) {
  error_stream << filename << ":" << t->get_line_number() << ": ";
  return semant_error();
}

ostream &ClassTable::semant_error() {
  semant_errors++;
  return error_stream;
}


void method_class::AddAttribute() {}
void attr_class::AddMethod() {}


Symbol attr_class::matchFormals(Formals actual) { return No_type; }
Symbol method_class::matchFormals(Formals actual) {
  Symbol type = return_type;
  for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
    Symbol actual_type = actual->nth(i)->get_typedecl();
    if (formals->more(i) == false) {
      return No_type;
    }
    Symbol declar_type = formals->nth(i)->get_typedecl();
    if (declar_type != actual_type) {
      return No_type;
    }
  }
  return type;
}

 //a class can override methods from ancestors but they have to have the
 //same number of formal parameters, the same types and the same return type
void method_class::AddMethod() {

  if (inheritEnv.lookup(name) != NULL) {
    Feature oldmethod = inheritEnv.lookup(name);
    Symbol oldret_type = oldmethod->matchFormals(formals);
    if (oldret_type == No_type || oldret_type != return_type) {
      classtable->semant_error(curclass) << "Invalid override\n";
    }
  }

  inheritEnv.addid(name, copy_Feature());
  methodEnv[curclass->get_name()].addid(name, copy_Feature());
}

//attribute cannot be self, cannot redifine ancestor's attributes
void attr_class::AddAttribute() {
  if (name == self)
    classtable->semant_error(curclass)
        << "attribue 'self' can not exist\n";
  else if (objectEnv.lookup(name) != NULL)
    classtable->semant_error(curclass)<< "Attribute " << name << " of an ancestor cannot be redefined"<< std::endl;
  objectEnv.addid(name, new Symbol(type_decl));
}

//formal parameter cannot be self
void formal_class::addFormal() {
  if (name == self) {
    classtable->semant_error(curclass)
        << "'self' cannot be the name of a formal parameter\n";
  }
  
  //formal parameter cannot have Self Type
  if (type_decl == SELF_TYPE) {
    classtable->semant_error(curclass)
        << "Formal parameter " << name << " cannot have type SELF_TYPE\n";
  }
  
  //formal parameters have to be distinct
  if (objectEnv.probe(name) != NULL)
    classtable->semant_error(curclass)
        << "Formal parameter " << name << " is multiply defined\n";
  objectEnv.addid(name, new Symbol(type_decl));
}

Symbol method_class::CheckFeatureType() {
  objectEnv.enterscope();
  for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
    Formal f = formals->nth(i);
    f->addFormal();
  }

  Symbol expr_type = expr->CheckExprType();
  Symbol type = expr_type;

  if (classtable->isSubtype(expr_type, return_type) == false) {
    classtable->semant_error(curclass)
        << "Inferred return type " << expr_type << " of method " << name
        << " does not conform to declared return type " << return_type
        << std::endl;
    type = Object;
  }

  objectEnv.exitscope();

  return type;
}

Symbol attr_class::CheckFeatureType() {
  Symbol expr_type = init->CheckExprType();
  if (expr_type == No_type)
    return type_decl;

  Symbol type = expr_type;
  if (classtable->isSubtype(expr_type, type_decl) == false) {
    classtable->semant_error(curclass) << "Error: feature assign invalid\n";
    type = Object;
  }
  return type;
}

Symbol assign_class::CheckExprType() {
  Symbol *lval = objectEnv.lookup(name);
  Symbol rval = expr->CheckExprType();

  type = rval;

  if (lval == NULL || name == self) {
    classtable->semant_error(curclass)
        << "Cannot assign to " << name << std::endl;
    type = Object;
    return type;
  }


  if (classtable->isSubtype(rval, *lval) == false) {
    classtable->semant_error(curclass) << "Error: assign rval not child\n";
    type = Object;
  }

  return type;
}

Symbol attr_class::matchFormals(Expressions e) { return No_type; }
Symbol method_class::matchFormals(Expressions actual) {

  Symbol type = return_type;
  for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
    Symbol actual_type = actual->nth(i)->CheckExprType();
    if (formals->more(i) == false) {
      return Object;
    }
    Symbol declar_type = formals->nth(i)->get_typedecl();
    if (classtable->isSubtype(actual_type, declar_type) == false) {
      classtable->semant_error(curclass) << "Error: unmatched formal type\n";
      type = Object;
    }
  }
  return type;
}

Symbol static_dispatch_class::CheckExprType() {
  Symbol expr_type = expr->CheckExprType();

  if (classtable->isSubtype(expr_type, type_name) == false) {
    classtable->semant_error(curclass)
        << "Expression type " << expr_type
        << " does not conform to declared static dispatch type " << type_name
        << std::endl;
    type = Object;
    return type;
  }

  Symbol ancestor = classtable->findMethodInAncestor(type_name, name);

  if (ancestor == No_class) {
    classtable->semant_error(curclass)
        << "Error: cannot find method " << name << std::endl;
    type = Object;
    return type;
  }

  Feature_class *method = methodEnv[ancestor].lookup(name);

  type = method->matchFormals(actual);

  if (type == SELF_TYPE)
    type = expr_type;
  return type;
}

Symbol dispatch_class::CheckExprType() {
  Symbol expr_type = expr->CheckExprType();

  Symbol ancestor = classtable->findMethodInAncestor(expr_type, name);

  if (ancestor == No_class) {
    classtable->semant_error(curclass)
        << "Error: method " << name << " does not exist" << std::endl;
    return Object;
  }

  Feature_class *method = methodEnv[ancestor].lookup(name);

  type = method->matchFormals(actual);

  if (type == SELF_TYPE)
    type = expr_type;
  return type;
}

Symbol cond_class::CheckExprType() {
  Symbol pred_type = pred->CheckExprType();
  if (pred_type != Bool)
    classtable->semant_error(curclass)
        << "Error: not boolean predicator\n";

  Symbol then_type = then_exp->CheckExprType();
  Symbol else_type = else_exp->CheckExprType();
  type = then_type;
  if (else_type != No_type)
    type = classtable->CommonAncestor(then_type, else_type);
  return type;
}

Symbol loop_class::CheckExprType() {
  type = pred->CheckExprType();
  if (type != Bool) {
    classtable->semant_error(curclass) << "Error: loop pred\n";
  }
  body->CheckExprType();
  type = Object;
  return type;
}

Symbol typcase_class::CheckExprType() {
  expr->CheckExprType();

  std::set<Symbol> s;

  int i = cases->first();
  type = cases->nth(i)->CheckBranchType();
  for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
    Case oneBranch = cases->nth(i);

    if (s.find(oneBranch->get_typedecl()) != s.end()) {
      classtable->semant_error(curclass) << "Error: branch has same type\n";
    }
    s.insert(oneBranch->get_typedecl());

    Symbol branch_type = oneBranch->CheckBranchType();
    type = classtable->CommonAncestor(type, branch_type);
  }
  return type;
}
Symbol neg_class::CheckExprType() {
  type = e1->CheckExprType();
  if (type != Int) {
    classtable->semant_error(curclass) << "Error: wrong neg format\n";
    type = Object;
  }
  return type;
}

Symbol block_class::CheckExprType() {
  type = Object;
  for (int i = body->first(); body->more(i); i = body->next(i)) {
    Expression e = body->nth(i);
    type = e->CheckExprType();
  }
  return type;
}

Symbol branch_class::CheckBranchType() {
  objectEnv.enterscope();
  objectEnv.addid(name, new Symbol(type_decl));

  Symbol type = expr->CheckExprType();

  objectEnv.exitscope();
  return type;
}

Symbol let_class::CheckExprType() {
  objectEnv.enterscope();
  if (identifier == self)
    classtable->semant_error(curclass)
        << "'self' cannot be bound in a 'let' expression\n";
  objectEnv.addid(identifier, new Symbol(type_decl));

  Symbol ini_type = init->CheckExprType();
  type = body->CheckExprType();

  if (ini_type != No_type)
    if (classtable->isSubtype(ini_type, type_decl) == false)
      classtable->semant_error(curclass) << "Error: dynamic type is not a subtype od static type\n";
  objectEnv.exitscope();

  return type;
}

Symbol plus_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();

  type = Int;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass) << "Error: wrong addition format\n";
    type = Object;
  }
  return type;
}

Symbol sub_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();

  type = Int;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass) << "Error: wrong substraction format\n";
    type = Object;
  }
  return type;
}

Symbol mul_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();

  type = Int;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass)
        << "Error: wrong multiplication format\n";
    type = Object;
  }
  return type;
}

Symbol divide_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();

  type = Int;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass) << "Error: wrong dividision format\n";
    type = Object;
  }
  return type;
}

Symbol lt_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();
  type = Bool;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass) << "Error: wrong less than format\n";
    type = Object;
  }
  return type;
}

Symbol comp_class::CheckExprType() {
  Symbol e1val = e1->CheckExprType();
  type = Bool;
  if (e1val != Bool) {
    classtable->semant_error(curclass) << "Error: wrong not format\n";
    type = Object;
  }
  return type;
}

Symbol eq_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();

  type = Bool;
  if (classtable->isBasic(lval) || classtable->isBasic(rval))
    if (lval != rval) {
      classtable->semant_error(curclass) << "wrong equal format\n";
      type = Object;
    }

  return type;
}

Symbol leq_class::CheckExprType() {
  Symbol lval = e1->CheckExprType();
  Symbol rval = e2->CheckExprType();
  type = Bool;
  if (lval != Int || rval != Int) {
    classtable->semant_error(curclass) << "Error: wrong less or equal format\n";
    type = Object;
  }
  return type;
}

Symbol int_const_class::CheckExprType() {
  type = Int;
  return type;
}
Symbol bool_const_class::CheckExprType() {
  type = Bool;
  return type;
}
Symbol string_const_class::CheckExprType() {
  type = Str;
  return type;
}

Symbol new__class::CheckExprType() {
  type = type_name;
  if (type != SELF_TYPE && classtable->getClassName(type_name) == NULL) {
    classtable->semant_error(curclass)
        << " Undefined return type " << type_name << std::endl;
    type = Object;
  }
  return type;
}

Symbol isvoid_class::CheckExprType() {
  e1->CheckExprType();
  type = Bool;
  return type;
}

Symbol no_expr_class::CheckExprType() {
  type = No_type;
  return type;
}

Symbol object_class::CheckExprType() {

  Symbol *found_type = objectEnv.lookup(name);

  if (found_type == NULL) {
    classtable->semant_error(curclass)
        << "Undeclared identifier " << name << std::endl;
    type = Object;
  } else
    type = *found_type;

  return type;
}


void program_class::checkClassesType(Symbol classname) {

  curclass = classtable->getClassName(classname);
  objectEnv.enterscope();
  objectEnv.addid(self, new Symbol(SELF_TYPE));
  Features fs = curclass->get_features();
  for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
    Feature curFeature = fs->nth(i);
    curFeature->AddAttribute();
  }

 
  if (!classtable->isBasic(classname)) {

    for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
      Feature curFeature = fs->nth(i);
      curFeature->CheckFeatureType();
    }
  }

  std::list<Symbol>::iterator iter;
  std::list<Symbol> nexClass = classtable->getChildren(classname);
  for (iter = nexClass.begin(); iter != nexClass.end(); ++iter)
    checkClassesType(*iter);

  objectEnv.exitscope();
}


 //inheritEnv records methods along current inheritance path
 
void program_class::install_Methods(Symbol classname) {

  curclass = classtable->getClassName(classname);
  inheritEnv.enterscope();
  methodEnv[classname].enterscope();
  Features fs = curclass->get_features();
  for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
    Feature curFeature = fs->nth(i);
    curFeature->AddMethod();
  }

  std::list<Symbol>::iterator iter;
  std::list<Symbol> nexClass = classtable->getChildren(classname);
  for (iter = nexClass.begin(); iter != nexClass.end(); ++iter)
    install_Methods(*iter);

  inheritEnv.exitscope();
}

void program_class::semant() {
  initialize_constants();

  /* ClassTable constructor may do some semantic analysis */
  classtable = new ClassTable(classes);

  /* some semantic analysis code may go here */

  install_Methods(Object);
  checkClassesType(Object);

  if (classtable->errors()) {
    cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
  }
}
