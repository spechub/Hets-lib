EXPORT = MonadSyntax.thy MultimonadSyntax.thy KleeneSyntax.thy OneStackReverse.thy TwoStackReverse.thy

StackReverse.tar: 
	mkdir StackReverse
	cp $(EXPORT) StackReverse
	tar -cf StackReverse.tar StackReverse
	rm -Rf StackReverse

rebuild: clean StackReverse.tar

upload: rebuild
	rcp StackReverse.tar pollux:/home/www/users/sergey/

clean:
	rm -f StackReverse.tar
