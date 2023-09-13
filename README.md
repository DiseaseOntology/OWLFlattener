# OWLFlattener
OWL Utility to flatten the hierarchical axioms down from ancestors to children

# Build instructions
1) Install Maven
2) Run: `mvn package`

You should now have a fat executable jar file in the target subdirectory.

# Usage:
```
Required options are -i and -r

usage: java -jar owl-flattener-0.0.1.jar
 -i,--owl <arg>     Path to the merged owl file
 -r,--root <arg>    Root IRI: eg: http://purl.obolibrary.org/obo/DOID_4
 -d,--debug         Turn on debug logging
 -h,--help
 -t,--trace <arg>   Trace inheritance; specify a space-separated list (eg.
                    DOID_001 DOID_002)```
