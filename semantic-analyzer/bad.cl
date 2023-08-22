class C {
	a : Int;
	b : Bool;
	init(x : Int, y : Bool) : C {
           {
		a <- x;
		b <- y;
		self;
           }
	};
};
class D inherits F{

	init(x : Int, y : Bool) : C {
           {
		a <- x;
		b <- y;
		self;
           }
	};
};
class F inherits D{

	init(x : Int, y : Bool) : C {
           {
		a <- x;
		b <- y;
		self;
           }
	};
};
Class Main{
	main():C {
	 {
	  (new C).init(1,1);
	  (new C).init(1,true,3);
	  (new C).iinit(1,true);
	  (new C);
	 }
	};
};
