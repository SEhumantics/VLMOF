abstract class Entry {
  key : String [1..1] unordered unique (id);
  catalog : Catalog [1..1] unordered unique;
}

class Book extends Entry {
  inPrint : Boolean [0..1] unordered unique;
  authors : Author [1..*] ordered unique;
}

class Author {
  name : String [1..1] unordered unique;
  books : Book [0..*] unordered unique;
}

class Catalog {
  entries : Entry [0..*] ordered unique composite;
}

association CatalogEntries {
  ends Catalog::entries, Entry::catalog;
}

association Authorship {
  ends Book::authors, Author::books;
}

object catalog : Catalog {
  observe Catalog::entries = [@book];
}

object book : Book {
  observe Entry::key = ["semantics"];
  observe Entry::catalog = [@catalog];
  observe Book::inPrint = [false];
  observe Book::authors = [@authorOne, @authorTwo];
}

object authorOne : Author {
  observe Author::name = ["A. Writer"];
  observe Author::books = [@book];
}

object authorTwo : Author {
  observe Author::name = ["B. Writer"];
  observe Author::books = [@book];
}
