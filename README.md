# captain-hook

Hive hooks are incredibly powerful, like a shotgun pointed at your foot.

This bit of code is a very very bad example of what a good engineer should do, but a very direct example of rewriting a query in motion

    hive> add jar target/captain-hook-1.0-SNAPSHOT.jar;
    hive> set hive.semantic.analyzer.hook=org.notmysock.hive.hooks.AndOrRewriteHook;
    
    hive> select * from ... where (a=1 and b=2) or (a=1 and b=3) ...;
