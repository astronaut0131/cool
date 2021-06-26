#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>
#include <map>
#include <set>
#include <vector>
#include <memory>
#include <algorithm>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"


#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;
using std::map;
using std::vector;
using std::set;
using std::unique_ptr;
// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  void construct_graph();
  void check_graph_acyclic();
  void check_all_parent_defined();
  void check_main_class();
  void check_class_redefinition();
  void add_method_declarations(Symbol node,Symbol parent);
  void add_attr_declarations(Symbol node);
  ostream& error_stream;
  Classes user_defined_classes = nil_Classes();
  Classes basic_classes = nil_Classes();
  Classes classes = nil_Classes();
  map<Symbol,vector<Symbol>> graph;
  map<Symbol,int> degree;
  map<Symbol,Symbol> parent;
  map<Symbol,class__class*> symbol_to_class;
public:
  ClassTable(Classes);
  ~ClassTable();
  bool has_type(Symbol type);
  int errors() { return semant_errors; }
  void check_inheritance();
  void type_checking_and_annotation();
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
  bool inheritance_leq(Symbol a,Symbol b);
  Symbol get_current_class_name() {
      auto cls = dynamic_cast<class__class*> (current_class);
      return cls->get_name();
  }
  Symbol least_common_ancestor(Symbol a,Symbol b);
  MySymbolTable<Symbol,Symbol> object_environment;
  map<Symbol,MySymbolTable<Symbol,vector<Symbol>>> function_environment;
  Class_ current_class;
  set<Symbol> basic_classes_set;
  set<Symbol> user_defined_classes_set;
};


#endif

