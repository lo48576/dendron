//! Tests to ensure that grants and prohibitions conflict expectedly.

mod prohibition_first {
    use dendron::{Node, StructureEditGrantError};

    #[test]
    fn frozen_node_prevents_hot_node_creation() {
        let root = Node::new_tree(());
        let frozen = root
            .clone()
            .bundle_new_structure_edit_prohibition()
            .expect("should success");
        assert!(matches!(
            root.clone().bundle_new_structure_edit_grant(),
            Err(StructureEditGrantError)
        ));

        drop(frozen);
        assert!(root.bundle_new_structure_edit_grant().is_ok());
    }
}

mod grant_first {
    use dendron::{Node, StructureEditProhibitionError};

    #[test]
    fn hot_node_prevents_frozen_node_creation() {
        let root = Node::new_tree(());
        let hot = root
            .clone()
            .bundle_new_structure_edit_grant()
            .expect("should success");
        assert!(matches!(
            root.clone().bundle_new_structure_edit_prohibition(),
            Err(StructureEditProhibitionError)
        ));

        drop(hot);
        assert!(root.bundle_new_structure_edit_prohibition().is_ok());
    }
}
