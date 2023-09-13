package edu.umaryland.igs.eng.disont.utils;

import edu.umaryland.igs.eng.disont.utils.OWLUtil;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.apache.commons.lang3.StringEscapeUtils;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.search.EntitySearcher;

import uk.ac.manchester.cs.owl.owlapi.OWLClassImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDeclarationAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLEquivalentClassesAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectExactCardinalityImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectMinCardinalityImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubClassOfAxiomImpl;

import org.json.simple.JSONObject;
import org.json.simple.JSONArray;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

/**
 * 
 * @author Mike Schor
 * 
 * This is the Disease Ontology project's OWL Flattener
 * 
 * This program flattens logical axioms down the tree from parents to children.
 * The output is a series of JSON elements to be posted to Elasticsearch which
 * drives the DO-KB's Faceted Search interface
 * 
 */

public class OWLFlattener {


	private static String ROOT_IRI = null;
	private OWLOntology ontology = null;
	private Set<OWLClassImpl> excludeSet = null;
	
	private Set<String> unhandledTypes = new HashSet<>();
	
	private String inputFile = null;
	
	private static boolean DEBUG = false;

	// PUT IDs into the TRACE_IDS array and set TRACE_MODE = true in order to only see output about specific terms.
	private static boolean TRACE_MODE = false;
	private static String[] TRACE_IDS = null; //eg: new String[] {"DOID_0001816"};

			

	private Map<OWLClass, Boolean> axiomParentsComplete = new HashMap<>();
	private Map<OWLClass, Set<OWLClass>> allParentsMap = new HashMap<>();
	private Set<String> parentStack = new HashSet<String>();
	
	public OWLFlattener(String owlFilename) throws OWLOntologyCreationException {
		File infile = new File(owlFilename);
		if (!infile.isFile()) {
			System.err.println("Failed to find input file: " + owlFilename);
			System.exit(1);
		}
		if (!infile.canRead()) {
			System.err.println("Input file does not have read permission: " + owlFilename);
			System.exit(1);
		}
		
		this.inputFile = owlFilename;
		
	}
	
	private String getIdFromOWLClass(OWLClass c) {
		Optional<String> idOpt = c.getIRI().getRemainder();
		if (idOpt.isPresent()) {
			String id = idOpt.get();
			id = id.replaceFirst("_", ":");
			return id;
		}
		return null;
	}
	
	private String getOWLClassName(OWLClass clazz, OWLOntology ontology) {
		Stream<OWLAnnotation> annotationStream = EntitySearcher.getAnnotations(clazz, ontology);
		Set<OWLAnnotation> classAnnotations = annotationStream.collect(Collectors.toSet());
	
		for (OWLAnnotation an : classAnnotations) {
			
			if (!an.getProperty().isDeprecated() && 
					an.getProperty().isLabel() &&
					!(an.getValue().literalValue().isPresent()
						&& an.getValue().literalValue().get().getLiteral().startsWith("obsolete ")))
			{
				
					return an.getValue().literalValue().get().getLiteral();
			}
		}
		return null;
	}
	
	
	private List<IRI> getIriFromOce(OWLClassExpression oce) {
		
		List<IRI> iris = new ArrayList<>();
		
		if (oce instanceof OWLObjectSomeValuesFromImpl) {
				
			OWLObjectSomeValuesFromImpl oosvfi = (OWLObjectSomeValuesFromImpl)oce;
			
			if (oosvfi.getFiller() instanceof OWLClassImpl) {
				iris.add(((OWLClassImpl) oosvfi.getFiller()).getIRI());
			}
			else {
				iris.addAll(getIriFromOce(oosvfi.getFiller()));
			}
		}
		else if (oce instanceof OWLClassImpl) {
			OWLClassImpl oci = (OWLClassImpl) oce;
			iris.add(oci.getIRI());
		}
		else if (oce instanceof OWLObjectMinCardinalityImpl) {
			OWLObjectMinCardinalityImpl oomc = (OWLObjectMinCardinalityImpl)oce;
			iris.addAll(getIriFromOce(oomc.getFiller()));
		}
		else if (oce instanceof OWLObjectIntersectionOfImpl) {
			OWLObjectIntersectionOfImpl ooioi = (OWLObjectIntersectionOfImpl)oce;
			
			Set<OWLClassExpression> oces = ooioi.getOperands();
			for (OWLClassExpression o : oces) {
				iris.addAll(getIriFromOce(o));
			}
		}
		else if (oce instanceof OWLObjectExactCardinalityImpl) {
			OWLObjectExactCardinalityImpl ooec = (OWLObjectExactCardinalityImpl)oce;
			iris.add(((OWLClassImpl)ooec.getFiller()).getIRI());
		}
		else {
			//TODO: Double check if this is a problem. Leave breakpoint here.
			if (OWLFlattener.DEBUG)
				System.out.println("Don't know how to get IRI from this type of oce: " + oce.toString());
			unhandledTypes.add(oce.toString());
		}
		
		return iris;
			
	}
	
	private String getLabel(IRI oc) {
		
    	Stream<OWLAnnotation> axiomAnnotationStream = EntitySearcher.getAnnotations(oc, ontology);
		Set<OWLAnnotation> axiomAnnotations = axiomAnnotationStream.collect(Collectors.toSet());
		
		String value = null;
		for (OWLAnnotation an : axiomAnnotations) {
			if (an.getProperty().isLabel()) {
				value = an.getValue().literalValue().get().getLiteral();
			}
		}
		return value;
		
	}
	private Set<OWLClass> getAllParentAxioms(OWLClass c) {
		
		// If we're in 'trace mode', we're trying to track down a question of relationships
		// We've probably turned on debug for specific terms and need to now get all parents
		// of this term again so we can see the logging output.
		
		if (OWLFlattener.DEBUG)
			System.out.println("Entered getAllParentAxioms for: " + c.toString());
		
		if (axiomParentsComplete.containsKey(c)) {
			if (OWLFlattener.DEBUG) {
				System.out.println("Already found these parents. Not re-calculating them, just returning the following:");
				if (allParentsMap.get(c) == null) {
					System.out.println(("No parents found"));
				}
				else {
					for (OWLClass owc : allParentsMap.get(c)) {
						System.out.println(owc.toString());
					}
				}
			}

			return allParentsMap.get(c);
		}
	
	
		Stream<OWLAnnotationAssertionAxiom> annoStream = EntitySearcher.getAnnotationAssertionAxioms(c, ontology);
		Set<OWLAnnotationAssertionAxiom> annos = annoStream.collect(Collectors.toSet());

		// This block pulls in ECO codes. They're not the same as the other codes. They are AnnotationAssertionAxioms
		ArrayList<IRI> annIriList = new ArrayList<>();
		for (OWLAnnotationAssertionAxiom aaa : annos) {
			Set<OWLAnnotation> anos = aaa.getAnnotations();
			for (OWLAnnotation ano : anos) {
				if (ano.getProperty().getIRI().getNamespace().equals("http://purl.org/dc/elements/1.1/") &&
						ano.getProperty().getIRI().getRemainder().get().equals("type")) {
					annIriList.add(ano.getValue().asIRI().get());
				}
			}
		}
		for (IRI i : annIriList) {
			if (OWLFlattener.DEBUG) {
				System.out.println("Pulling in IRI: " + i.toString() + "(" + getLabel(i) + ")");
			}
			OWLClass subClass = OWLManager.getOWLDataFactory().getOWLClass(i);
			if (!allParentsMap.containsKey(c)) {
				allParentsMap.put(c, new HashSet<>());
			}
			if (OWLFlattener.DEBUG) {
				System.out.println("Adding subclass: " + subClass.toString());
			}
			allParentsMap.get(c).add(subClass);	
		}

		// Get all class axioms. For some reason, we get 
		Stream<OWLAxiom> axiomStream = EntitySearcher.getReferencingAxioms(c, this.ontology);
		Set<OWLAxiom> classAxioms = axiomStream.collect(Collectors.toSet());
		
		
		for (OWLAxiom a : classAxioms) {

			// Apparently, "referencing axioms" go both ways. 
			// In includes axioms that reference this class and axioms that this class references.
			// We're only interested in the ones that this current class references.
			// So we'll check each axiom here and continue if the direction is wrong.
			if (a instanceof OWLSubClassOfAxiomImpl ) {
				OWLSubClassOfAxiomImpl ascoai = (OWLSubClassOfAxiomImpl)a;
				OWLClassExpression subClass = ascoai.getSubClass();
				if (subClass instanceof OWLClassImpl) {
					if (!((OWLClassImpl)subClass).getIRI().toString().equals(c.getIRI().toString())) {
						if (OWLFlattener.DEBUG) {
							System.out.println("Incorrect axiom direction: " + a.toString());
						}
						continue;
					}
				}
				else {
					//wrong direction. Superclass must be an OWLClassImpl and == this OWLClass
					System.out.println("Incorrect axiom direction: " + a.toString());
					continue;
				}

			}

			if (OWLFlattener.DEBUG) {
				System.out.println("Examining axiom " + a.toString()); // + " which is directly on class " + c.toString());
			}
			
			if (a instanceof OWLDeclarationAxiomImpl) {
				// this is the same as the class; continue to the next axiom
				if (OWLFlattener.DEBUG)
					System.out.println("Skipping declaration");
				continue;
			}

			// This list is going to hold all of the IRI's (the OWL Classes) that we're going to need to both add in as a facet value
			// and also follow up the tree to pull in more and more ancestor facet values.
			ArrayList<IRI> iriList = new ArrayList<>();
			
			// for some reason, most axioms are of type "SubClass", but these axioms contain a reference to the "SuperClass"; and that's really what we're interest in here.
			if (a instanceof OWLSubClassOfAxiomImpl ) {
				OWLSubClassOfAxiomImpl ascoai = (OWLSubClassOfAxiomImpl)a;
				OWLClassExpression superClass = ascoai.getSuperClass();
				
				// handle basic OWL Class
				if (superClass instanceof OWLClassImpl) {
					OWLClassImpl aAsC = (OWLClassImpl)superClass;
					iriList.add(aAsC.getIRI());
				}
				// handle Some Values From axiom
				else if (superClass instanceof OWLObjectSomeValuesFromImpl) {
					// This is considered an "Anonymous SubClass". If it's not a DO term, but instead a term from one of the
					// merged-in ontologies, then don't bring in this one.
					if (!c.getIRI().getRemainder().get().startsWith("DOID")) {
						if (OWLFlattener.DEBUG)
							System.out.println("Skipping anonymous subclass");
						continue;
					}
					OWLObjectSomeValuesFromImpl superSomeValuesFrom = (OWLObjectSomeValuesFromImpl) superClass;	
					if (superSomeValuesFrom.getFiller() instanceof OWLObjectUnionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectUnionOfImpl) superSomeValuesFrom.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
					else if (superSomeValuesFrom.getFiller() instanceof OWLObjectIntersectionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectIntersectionOfImpl) superSomeValuesFrom.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
					else {
						iriList.add(superSomeValuesFrom.getFiller().asOWLClass().getIRI());
					}
				}
				// handle Min Cardinality axiom
				else if (superClass instanceof OWLObjectMinCardinalityImpl) {
					OWLObjectMinCardinalityImpl oomci = (OWLObjectMinCardinalityImpl)superClass;
					if (oomci.getFiller() instanceof OWLObjectUnionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectUnionOfImpl) oomci.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
					else if (oomci.getFiller() instanceof OWLObjectIntersectionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectIntersectionOfImpl) oomci.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
				}
				// handle exact cardinality
				else if (superClass instanceof OWLObjectExactCardinalityImpl) {
					OWLObjectExactCardinalityImpl ooeci = (OWLObjectExactCardinalityImpl)superClass;
					if (ooeci.getFiller() instanceof OWLObjectUnionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectUnionOfImpl) ooeci.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
					else if (ooeci.getFiller() instanceof OWLObjectIntersectionOfImpl) {
						Set<OWLClassExpression> oces = ((OWLObjectIntersectionOfImpl) ooeci.getFiller()).getOperands();
						for (OWLClassExpression oce : oces) {
							iriList.addAll(getIriFromOce(oce));
						}
					}
				}

				// handle Intersection Of axiom
				else if (superClass instanceof OWLObjectIntersectionOfImpl) {
					OWLObjectIntersectionOfImpl ooioi = (OWLObjectIntersectionOfImpl)superClass;
					Set<OWLClassExpression> oces = ooioi.getOperands();
					for (OWLClassExpression oce : oces) {
						iriList.addAll(getIriFromOce(oce));
					}
				}
				
				else if (superClass instanceof OWLObjectUnionOfImpl) {
					OWLObjectUnionOfImpl oouoi = (OWLObjectUnionOfImpl)superClass;
					Set<OWLClassExpression> oces = oouoi.getOperands();
					for (OWLClassExpression oce : oces) {
						iriList.addAll(getIriFromOce(oce));
					}
				}
				
				/* This adds strange things to the output. For example, angiosarcoma gets 'oral cavity' and 'lung' as anatomy fields
				else if (ascoai.getSuperClass() instanceof OWLObjectIntersectionOfImpl) {
					OWLObjectIntersectionOfImpl intersection = (OWLObjectIntersectionOfImpl)ascoai.getSuperClass();
					// deprecated, use the stream method instead... however that works.
					Set<OWLClassExpression> oces = intersection.getOperands();
					for (OWLClassExpression oce : oces) {
						if (oce instanceof OWLObjectSomeValuesFromImpl) {
							
							OWLObjectSomeValuesFromImpl oosvfi = (OWLObjectSomeValuesFromImpl)oce;
							if (oosvfi.getFiller() instanceof OWLClassImpl) {
								iri = ((OWLClassImpl) oosvfi.getFiller()).getIRI();
								iriList.add(iri);
							}
							else {
								System.out.println("UNHANDLED: " + oosvfi.getFiller().toString());
								continue;
							}			
						}
					}
				}
                */
				else {
					if (OWLFlattener.DEBUG && !OWLFlattener.TRACE_MODE)
						//TODO: Put debug breakpoint here and share with Allen
						System.out.println("Unfollowed relationship: " + a.toString() + " -- while processing: " + c.toString());
					unhandledTypes.add(a.toString());
					if (OWLFlattener.DEBUG)
						System.out.println("Skipping unhandled relationship");
					continue;
				}
			}
			else if (a instanceof OWLEquivalentClassesAxiom) {
				Collection<OWLSubClassOfAxiom> subClassesOfAxiom = ((OWLEquivalentClassesAxiomImpl) a).asOWLSubClassOfAxioms();
				for (OWLSubClassOfAxiom owlSubClassOfAxiom: subClassesOfAxiom) {
					if ((owlSubClassOfAxiom.getSubClass() instanceof OWLClassImpl) 
							&& !((OWLClass)owlSubClassOfAxiom.getSubClass()).getIRI().getRemainder().get().equals(c.getIRI().getRemainder().get())) {
						continue;
					}
					if (owlSubClassOfAxiom.getSuperClass() instanceof OWLObjectIntersectionOfImpl) {
						OWLObjectIntersectionOfImpl intersection = (OWLObjectIntersectionOfImpl)owlSubClassOfAxiom.getSuperClass();
						if (OWLFlattener.DEBUG) {
							System.out.println("HERE");
						}
						Set<OWLClassExpression> oces = intersection.getOperands();
						for (OWLClassExpression oce : oces) {
							if (oce instanceof OWLObjectSomeValuesFromImpl) {
								
								OWLObjectSomeValuesFromImpl oosvfi = (OWLObjectSomeValuesFromImpl)oce;
								if (oosvfi.getFiller() instanceof OWLClassImpl) {
									iriList.add(((OWLClassImpl) oosvfi.getFiller()).getIRI());
								}
								else {
									if (OWLFlattener.DEBUG)
										System.out.println("UNHANDLED: " + oosvfi.getFiller().toString());
									unhandledTypes.add(oosvfi.toString());
									continue;
								}			
							}
						}
						
					}
					
					/* 
					 * Removing this type of axiom import. If the subClass is an intersection of the current term & something else, then that means that you'd have to combine
					 * some other disease term with something else in order to equal this guy (since we're looking at OWLEquivalentClassesAxiom in this block)
					 * That's not an equivalence. For example, 
					 * 	while examining Class DOID:178 (Vascular Disease), we get an equivalent axiom of DOID:2462 (retinal vascular disease) AND has location some retina
					 * Well, we don't want to bring "retina" back to "vascular disease"
					 *  
					 *  
					else if (owlSubClassOfAxiom.getSubClass() instanceof OWLObjectIntersectionOfImpl) {
						OWLObjectIntersectionOfImpl intersection = (OWLObjectIntersectionOfImpl)owlSubClassOfAxiom.getSubClass();
						// deprecated, use the stream method instead... however that works.
						Set<OWLClassExpression> oces = intersection.getOperands();
						for (OWLClassExpression oce : oces) {
							if (oce instanceof OWLObjectSomeValuesFromImpl) {
								
								OWLObjectSomeValuesFromImpl oosvfi = (OWLObjectSomeValuesFromImpl)oce;
								if (oosvfi.getFiller() instanceof OWLClassImpl) {
									iri = ((OWLClassImpl) oosvfi.getFiller()).getIRI();
									iriList.add(iri);
								}
								else {
									System.out.println("UNHANDLED: " + oosvfi.getFiller().toString());
									continue;
								}			
							}
						}
					}
                    */
					
					else {
						unhandledTypes.add(a.toString());
						continue;
					}
				}
				if (iriList.size() == 0) {
					continue;
				}
			}
			else {
				if (OWLFlattener.DEBUG)
					System.out.println("Unhandled instance type for axiom: " + a.toString());
					unhandledTypes.add(a.toString());
				continue;
			}
			
			
			if (iriList.size() == 0 || (iriList.size() == 1 && iriList.get(0).getRemainder().equals(c.getIRI().getRemainder()))) {
				// if the iri of the superclass is the same as the class itself, continue
				continue;
			}

			// We've now populated the iriList with all "referencing axioms", however, we only really want
			// some of these. So now we will pare down these IRIS.
			// For example, we don't want the ROOT IRI or any of the direct children of the root.
			// We also don't want to pull in IRIs for non-DO terms that are from a different ontology.
			// E.g. we don't want to pull in the related diseases (DOID IRIs) from UBERON:0001017. We only want
			// non-DO terms to pull in like terms (from the same ontology)
			
			List<IRI> removals = new ArrayList<>();
			for (IRI iri : iriList) {
				if (!c.getIRI().getRemainder().get().startsWith("DOID")) {
					if (iri.getRemainder().get().startsWith("DOID")) {
						removals.add(iri);
					}
				}
				if (iri.getRemainder().get().equals(OWLFlattener.ROOT_IRI)) {
					// found root; continue
					removals.add(iri);
				}
				boolean excludeTerm = false;
				for (OWLClassImpl oci : this.excludeSet) {
					if (iri.getRemainder().get().equals(oci.getIRI().getRemainder().get())) {
						excludeTerm = true;
						break;
					}
				}
				if (excludeTerm) {
					if (OWLFlattener.DEBUG)
						System.out.println("IRI: " + iri.getRemainder().get() + " was in the exclude list");
					removals.add(iri);
				}
			}
			iriList.removeAll(removals);
			

			// Now that we have identified all IRIs on this term, we're going to pull in all parent
			// IRIs for each one using this same method.
			for (IRI i : iriList) {
				if (OWLFlattener.DEBUG) {
					System.out.println("FROM " + a.toString() + " Pulling in IRI: " + i.toString() + "(" + getLabel(i) + ")");
				}
				
				OWLClass subClass = OWLManager.getOWLDataFactory().getOWLClass(i);
				
				if (!allParentsMap.containsKey(c)) {
					allParentsMap.put(c, new HashSet<>());
				}
				allParentsMap.get(c).add(subClass);
				
				// prevent cyclical follows
				if (!parentStack.contains(subClass.getIRI().getRemainder().get())) { 
					parentStack.add(subClass.getIRI().getRemainder().get());
					if (OWLFlattener.DEBUG)
						System.out.println("About to get all parent axioms for " + i.toString());
					
					Set<OWLClass> parentAxioms = getAllParentAxioms(subClass);
					if (OWLFlattener.DEBUG)
						System.out.println("Finished getting all parent axioms for " + i.toString());

					if (parentAxioms != null) {
						allParentsMap.get(c).addAll(parentAxioms);
					}
					parentStack.remove(subClass.getIRI().getRemainder().get());
				}
			}
			
			axiomParentsComplete.put(c, true);
		}
		
		return allParentsMap.get(c);
	}
	
	//TODO: Was going to use this to sort the json arrays in the output, but this is on hold until it might be needed.
	private void insertValToJSONArray(JSONArray ja, String value) {
	
		int position = 0;
		for (Object o : ja) {
			if (((String)o).compareTo(value) > 0) {
				position += 1;
			}
		}
		ja.add(position, value);
		
	}
	
	public void parse() throws OWLOntologyCreationException, IOException {
		

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = this.load(manager);
        this.ontology = ontology;
        
        this.excludeSet = getDirectRootChildren(manager);
        
		final String DEFINITION = OWLUtil.getAnnotationThatSignifiesDefinition(this.ontology);

		
        ArrayList<OWLClass> classes = new ArrayList<OWLClass>();
        ontology.classesInSignature().forEach(classes::add);
        
        int i = 0;
        int obs = 0;
        int no_axioms = 0;
        int no_non_doid_axioms = 0;
        int no_name = 0;
        List<String> noNames = new ArrayList<>();
        List<String> onlyDOIDAxioms = new ArrayList<>();
        List<String> noAxioms = new ArrayList<>();
    
        String outputFileName = "outputfile.json";
//      FileWriter xmlWriter = new FileWriter(outputFileName + ".xml");
        FileWriter jsonWriter = new FileWriter(outputFileName);
//      xmlWriter.write("<add>\n");
        

        System.out.println("Successfully opened output file for writing: " + outputFileName);
      
        
        for (OWLClass c : classes) {

        	if (OWLFlattener.TRACE_MODE) {
	        	if (Arrays.asList(TRACE_IDS).contains(c.getIRI().getRemainder().get()) && OWLFlattener.DEBUG == false) {
					OWLFlattener.DEBUG = true;
					System.out.println("TURNING DEBUG: ON");
				}
				else if (OWLFlattener.DEBUG == true) {
					OWLFlattener.DEBUG = false;
					System.out.println("TURNING DEBUG: OFF");
				}
        	}
        	
        	String id = getIdFromOWLClass(c);
			
			if (id != null && id.startsWith("DOID:")) {
				
				i += 1;
				String disease = getOWLClassName(c, ontology);
				if (disease == null) {
					//TODO: Uncomment this to see doids without class names -- later
					if (!OWLFlattener.TRACE_MODE && OWLFlattener.DEBUG) 
						System.out.println("Disease with null name. Possibly deprecated / obsolete: " + id);
					no_name += 1;
					noNames.add(c.getIRI().getRemainder().get());
					continue;
				}
			}
			else {
				//System.out.println("ID was not a DOID: " + id);
				continue;
			}
	        
	        
			Set<OWLClass> parentAxioms = getAllParentAxioms(c);
			
			String name = null;
			String definition = null;
			boolean isDocStarted = false;
			
			Stream<OWLAnnotation> annotationStream = EntitySearcher.getAnnotations(c, ontology);
			Set<OWLAnnotation> classAnnotations = annotationStream.collect(Collectors.toSet());
			boolean obsolete = false;
			// for each class, we'll need to iterate over all of the Annotations. These will give us things we need such as:
			// the class' name, obsolete / deprecated flag, xrefs, alternativeIds, synonyms, subsets, and the definition 
			for (OWLAnnotation an : classAnnotations) {
				if (an.getProperty().isDeprecated()) {
					obsolete = true;
					break;
				}
				else if (an.getProperty().isLabel()) {
					
					if (an.getValue().literalValue().isPresent()
							&& an.getValue().literalValue().get().getLiteral().startsWith("obsolete "))
					{
						obsolete = true;
						break;
					}
					else {
						// capture the name
						name = an.getValue().literalValue().get().getLiteral();
					}
				}
				else if (an.getProperty().getIRI().getRemainder().get().equals(DEFINITION)) {
					definition = an.getValue().literalValue().get().getLiteral();
					//definition needs to also be surrounded by a double quote. Just what the rendering code expects.
					definition = "\"" + definition + "\"";
				}
			}
			
			//TODO: Do we want to write out DO term that has no facet values? I don't think it would make sense, but
			// we should keep track of these
			JSONObject data = new JSONObject();
			
			if (!obsolete) {
				
				boolean non_doid_axiom_found = false;
				
				if (!isDocStarted) {
					isDocStarted = true;
//						xmlWriter.write("<doc>\n");
//						xmlWriter.write("\t<field name=\"id\">" + c.getIRI().getRemainder().get() + "</field>\n");
//						xmlWriter.write("\t<field name=\"name\">" + name + "</field>\n");
					
					jsonWriter.write("{ \"create\":{ } }\n");
					
					data.put("id", c.getIRI().getRemainder().get());
					data.put("name", name);
					

					//Some diseases don't have a definition
					if (definition == null) {
						if (OWLFlattener.DEBUG)
							System.out.println(c.getIRI() + " doesn't have a definition");
						
					}
					else {
						String safeDef = definition.replaceAll("<",  "&lt;").replaceAll(">", "&gt;");
//							xmlWriter.write("\t<field name=\"definition\">" + safeDef+ "</field>\n");
//							jsonWriter.write(",\"definition\": " + definition);
						if (definition.contains("\n")) {
							definition = definition.replace("\n", "");
						}
						data.put("definition", definition);
					}
				}
				
				if (parentAxioms == null || parentAxioms.size() == 0) {
					if (OWLFlattener.DEBUG)
						System.out.println("No parent axioms for: " + c.getIRI().getRemainder().get());
					no_axioms += 1;
					noAxioms.add(c.getIRI().getRemainder().get());
				}
				else {
				
					for (OWLClass oc : parentAxioms) {
						if (oc.getIRI().getRemainder().get().startsWith("DOID_")) {
							// avoid writing parent axioms that are DOIDs
							continue;
						}
						else {
							non_doid_axiom_found = true;
						}
			        	
			        	
			        	Stream<OWLAnnotation> axiomAnnotationStream = EntitySearcher.getAnnotations(oc, ontology);
						Set<OWLAnnotation> axiomAnnotations = axiomAnnotationStream.collect(Collectors.toSet());
						
						String value = null;
						for (OWLAnnotation an : axiomAnnotations) {
							if (an.getProperty().isLabel()) {
								value = an.getValue().literalValue().get().getLiteral();
							}
						}

						String safeValue = StringEscapeUtils.escapeXml(value);
						
						if (oc.getIRI().getRemainder().get().startsWith("UBERON")) {
//			        		xmlWriter.write("\t<field name=\"anatomy\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"anatomy\": \"" + safeValue + "\"");
			        		if ( data.get("anatomy") == null ) { data.put("anatomy", new JSONArray()); }
			        		((JSONArray) data.get("anatomy")).add(value);
			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("CL")) {
//							xmlWriter.write("\t<field name=\"cell_type\">" + safeValue + "</field>\n");
//							jsonWriter.write(",\"cell_type\": \"" + safeValue + "\"");
			        		if ( data.get("cell_type") == null ) { data.put("cell_type", new JSONArray()); }
			        		((JSONArray) data.get("cell_type")).add(value);

						}
						else if (oc.getIRI().getRemainder().get().startsWith("CHEBI")) {
//			        		xmlWriter.write("\t<field name=\"chebi\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"chebi\": \"" + safeValue + "\"");
			        		if ( data.get("chebi") == null ) { data.put("chebi", new JSONArray()); }
			        		((JSONArray) data.get("chebi")).add(value);
			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("SYMP")) {
//			        		xmlWriter.write("\t<field name=\"symptom\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"symptom\": \"" + safeValue + "\"");
			        		if ( data.get("symptom") == null ) { data.put("symptom", new JSONArray()); }
			        		((JSONArray) data.get("symptom")).add(value);
			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("DISDRIV")) {
//			        		xmlWriter.write("\t<field name=\"disease_driver\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"disease_driver\": \"" + safeValue + "\"");
			        		if ( data.get("disease_driver") == null ) { data.put("disease_driver", new JSONArray()); }
			        		((JSONArray) data.get("disease_driver")).add(value);
			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("ECO")) {
//			        		xmlWriter.write("\t<field name=\"evidence\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"evidence\": \"" + safeValue + "\"");
			        		if ( data.get("evidence") == null ) { data.put("evidence", new JSONArray()); }
			        		((JSONArray) data.get("evidence")).add(value);
			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("FOODON")) {
//			        		xmlWriter.write("\t<field name=\"food_material\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"food_material\": \"" + safeValue + "\"");
			        		if ( data.get("food_material") == null ) { data.put("food_material", new JSONArray()); }
			        		((JSONArray) data.get("food_material")).add(value);

			        	}
						else if (oc.getIRI().getRemainder().get().startsWith("GENO")) {
//			        		xmlWriter.write("\t<field name=\"inheritance_pattern\">" + safeValue + "</field>\n");
//			        		jsonWriter.write(",\"inheritance_pattern\": \"" + safeValue + "\"");
			        		if ( data.get("inheritance_pattern") == null ) { data.put("inheritance_pattern", new JSONArray()); }
			        		((JSONArray) data.get("inheritance_pattern")).add(value);
			        	}
						
						else if (oc.getIRI().getRemainder().get().startsWith("NCBITaxon")) {
//							xmlWriter.write("\t<field name=\"ncbitaxon\">" + safeValue + "</field>\n");
//							jsonWriter.write(",\"ncbitaxon\": \"" + safeValue + "\"");
							if ( data.get("ncbitaxon") == null ) { data.put("ncbitaxon", new JSONArray()); }
			        		((JSONArray) data.get("ncbitaxon")).add(value);
						}
						else if (oc.getIRI().getRemainder().get().startsWith("OMIM")) {
//							xmlWriter.write("\t<field name=\"omim_susceptibility\">" + safeValue + "</field>\n");
//							jsonWriter.write(",\"omim_susceptibility\": \"" + safeValue + "\"");
							if ( data.get("omim_susceptibility") == null ) { data.put("omim_susceptibility", new JSONArray()); }
			        		((JSONArray) data.get("omim_susceptibility")).add(value);
						}
						
						else if (oc.getIRI().getRemainder().get().startsWith("HP")) {
							if (safeValue.toLowerCase().contains("onset")) {
//								xmlWriter.write("\t<field name=\"onset\">" + safeValue + "</field>\n");
//								jsonWriter.write(",\"onset\": \"" + safeValue + "\"");
								if ( data.get("onset") == null ) { data.put("onset", new JSONArray()); }
				        		((JSONArray) data.get("onset")).add(value);
							}
							else {
//								xmlWriter.write("\t<field name=\"phenotype\">" + safeValue + "</field>\n");
//								jsonWriter.write(",\"phenotype\": \"" + safeValue + "\"");
								if ( data.get("phenotype") == null ) { data.put("phenotype", new JSONArray()); }
				        		((JSONArray) data.get("phenotype")).add(value);
							}
						}
						else if (oc.getIRI().getRemainder().get().startsWith("SO")) {
//							xmlWriter.write("\t<field name=\"sequence\">" + safeValue + "</field>\n");
//							jsonWriter.write(",\"sequence\": \"" + safeValue + "\"");
							if ( data.get("sequence") == null ) { data.put("sequence", new JSONArray()); }
			        		((JSONArray) data.get("sequence")).add(value);
						}
						else if (oc.getIRI().getRemainder().get().startsWith("TRANS")) {
//							xmlWriter.write("\t<field name=\"transmission_process\">" + safeValue + "</field>\n");
//							jsonWriter.write(",\"transmission_process\": \"" + safeValue + "\"");
							if ( data.get("transmission_process") == null ) { data.put("transmission_process", new JSONArray()); }
			        		((JSONArray) data.get("transmission_process")).add(value);
						}
			        }
				}
				
				if (non_doid_axiom_found == false) {
					no_non_doid_axioms += 1;
					onlyDOIDAxioms.add(c.getIRI().getRemainder().get());
				}
			}
			else {
				
				obs += 1;
			}
			
			

			if (isDocStarted) {
				jsonWriter.write(data.toJSONString());
				jsonWriter.write("\n");
			}
        }
        
        jsonWriter.close();
        
        
        System.out.println("There were " + no_non_doid_axioms + " records with only DOID axioms. These will only show up in the faceted search if no facets are selected.");
        if (OWLFlattener.DEBUG) {
	        for (String id : onlyDOIDAxioms) {
	        	System.out.println(id);
	        }
        }

        
        System.out.println("There were " + no_name + " records with no name (skipped)");
        if (OWLFlattener.DEBUG) {
	        for (String id : noNames) {
	        	System.out.println(id);
	        }
        }
        
        System.out.println("There were " + no_axioms + " records with no axioms. These will only show up in the faceted search if no facets are selected.");
        if (OWLFlattener.DEBUG) {
	        for (String na : noAxioms) {
	        	System.out.println(na);
	        }
        }
        else {
            System.out.println("\nRun with --debug to see these lists\n");
        }
        
        System.out.println("Processed " + i + " disease records");
        
        if (OWLFlattener.DEBUG) {
	        for (String s : unhandledTypes) {
	        	System.out.println("Unhandled Axiom type: " + s);
	        }
        }

        
        System.out.println("Created Elastic input file at: " + outputFileName);
        
        
    }

	/*
	 * Due to certain circumstances that I do not fully understand, we have chosen to 
	 * exclude axioms on the set of disease terms that are direct children of the root
	 * node. I believe this was bringing in too many IRIs.
	 */
    private Set<OWLClassImpl> getDirectRootChildren(OWLOntologyManager manager) {
    	

    	IRI iri = IRI.create(OWLFlattener.ROOT_IRI);

    	OWLClass root = manager.getOWLDataFactory().getOWLClass(iri);
    	if (OWLFlattener.DEBUG) {
    		System.out.println("Identified root node");
    		System.out.println(root);
    	}
    	
		Stream<OWLClassExpression> classesStream = EntitySearcher.getSubClasses(root, ontology);
		Set<OWLClassExpression> oces = classesStream.collect(Collectors.toSet());
		Set<OWLClassImpl> classes = new HashSet<>();
		
		for (OWLClassExpression oce : oces) {
			if (oce instanceof OWLClassImpl) {
				classes.add((OWLClassImpl)oce);
			}
			else {
				System.err.println("Expected all children of root to be an OWLClassImpl");
				System.err.println(oce);
				System.exit(1);
			}
		}
		
    	return classes;
		
	}

    
    private OWLOntology load(OWLOntologyManager manager) throws OWLOntologyCreationException {
    	
        return manager.loadOntologyFromOntologyDocument(new File(this.inputFile));
    }
    
	public static void main(String[] args) throws Exception {
		
		String owlFile = null;
		
		Options options = new Options();
        Option owlOpt = Option.builder("i")
            .required(true)
            .desc("Path to the merged owl file")
            .longOpt("owl")
            .hasArg()
            .build();

        Option rootOpt = Option.builder("r")
            .required(true)
            .desc("Root IRI: eg: http://purl.obolibrary.org/obo/DOID_4")
            .longOpt("root")
            .hasArg()
            .build();
        
        Option debugOpt = Option.builder("d")
                .required(false)
                .desc("Turn on debug logging")
                .longOpt("debug")
                .build();
        
        Option traceOpt = Option.builder("t")
                .required(false)
                .desc("Trace inheritance; specify a space-separated list (eg. DOID_001 DOID_002)")
                .longOpt("trace")
                .hasArgs()
                .build();
        
        Option helpOption = Option.builder("h")
                .longOpt("help")
                .required(false)
                .hasArg(false)
                .build();

        
        options.addOption(owlOpt);
        options.addOption(rootOpt);
        options.addOption(debugOpt);
        options.addOption(traceOpt);
        options.addOption(helpOption);
        
        
        CommandLineParser parser = new DefaultParser();
        
        try {
        	
        	// before parsing the args, check if there's a -h or --help present:
        	for (String s : args) {
        	    if (s.equals("-h") || s.equals("--help")) {
        	    	HelpFormatter formatter = new HelpFormatter();
                    formatter.printHelp("java -jar owl-flattener.jar", options);
        	        System.exit(1);
        	    }
        	}
        	
            // parse the command line arguments
            CommandLine cmdLine = parser.parse(options, args);

            if (cmdLine.hasOption("debug"))
            	OWLFlattener.DEBUG = true;

            if (cmdLine.hasOption("trace")) {
                OWLFlattener.TRACE_IDS = cmdLine.getOptionValues("trace");
                OWLFlattener.TRACE_MODE = true;
                OWLFlattener.DEBUG = false; //turn off debug when tracing
            }
            
            OWLFlattener.ROOT_IRI = cmdLine.getOptionValue("root");
            
            owlFile = cmdLine.getOptionValue("owl");
            
        }
        catch (ParseException exp) {
        	
            System.out.println("Error: " + exp.getMessage());
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("java -jar owl-flattener.jar", options);
            System.exit(1);
        }
		
		System.out.println("Beginning OWL processing at: " + new Date());
		System.out.println("Reading " + owlFile);
		

		OWLFlattener flattener = new OWLFlattener(owlFile);
		flattener.parse();
		
		System.out.println("Complete. Exiting at: " + new Date());
	}
}


