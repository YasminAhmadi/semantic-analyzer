#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"
#include <list>
#include <map>

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream &error_stream;
    
  std::map<Symbol, Class_> classmap;
  std::map<Symbol, std::list<Symbol> > ingraph;
  void incyc(Class_ cur, Classes classes, std::map<Class_, int> &map, bool &e, bool &c);

public:
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream &semant_error();
  ostream &semant_error(Class_ c);
  ostream &semant_error(Symbol filename, tree_node *t);
  bool isBasic(Symbol);
  bool isSubtype(Symbol, Symbol);
  std::list<Symbol> getChildren(Symbol classname) {
    return ingraph[classname];
  }
  Class_ getClassName(Symbol classname) {
    if (classmap.find(classname) == classmap.end())
      return NULL;
    return classmap[classname];
  }
  Symbol CommonAncestor(Symbol, Symbol);
  Symbol findMethodInAncestor(Symbol, Symbol);

};

#endif