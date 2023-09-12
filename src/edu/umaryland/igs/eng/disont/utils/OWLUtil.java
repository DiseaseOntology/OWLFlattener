package edu.umaryland.igs.eng.disont.utils;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.search.EntitySearcher;

public class OWLUtil {

	public static String getAnnotationLabel(Stream<OWLAnnotation> annotationStream) {
		Set<OWLAnnotation> classAnnotations = annotationStream.collect(Collectors.toSet());
		String label = null;
		for (OWLAnnotation an : classAnnotations) {
			if (an.getProperty().isLabel()) { // Found the label we want to go with this IRI
				label = an.getValue().literalValue().get().getLiteral();
				break;
			}
		}
		return label;
	}
	
	public static String getAnnotationThatSignifiesDefinition(OWLOntology ontology) {
		Set<OWLAnnotationProperty> aps = ontology.annotationPropertiesInSignature().collect(Collectors.toSet());
		String definition = null;
		for (OWLAnnotationProperty ap : aps) {
			Set<OWLAnnotation> annotations = EntitySearcher.getAnnotations(ap, ontology).collect(Collectors.toSet());
			for (OWLAnnotation an : annotations) {
				if (an.getValue().literalValue().isPresent() &&
						( an.getValue().literalValue().get().getLiteral().equals("definition") ||
						  an.getValue().literalValue().get().getLiteral().equals("textual definition"))) {
					// This is the annotation to use for definitions. Found it. Keep it safe.
					definition = ap.getIRI().getRemainder().get();
					break;
				}
			}
			if (definition != null)
				break;
		}
		
		return definition;
	}
}
