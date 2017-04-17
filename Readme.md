Gist Readme
===========

Summary
-------

Gist is a crude natural language parser. It's designed, not to
determine the precise nuanced meaning of long passages, but to
extract important ideas from short passages such as RSS newsfeed
summaries.

Gist uses a simple context free grammar to describe common grammar
structures, and relies on a vocab list to determine the parts of
speech for various words. It passes passages through preprocess
functions that strip out complicating information and then tries to
make sense of what remains.

While obviously, Gist misses a lot, its strength comes from the fact
that it can be used to answer questions.

Example Use
-----------

    Gist 'tmp.ttl' 'The dog ate the cat.'

Author
------

* Larry D. Lee jr. <llee454@gmail.com>

