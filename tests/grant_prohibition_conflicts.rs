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

    #[test]
    fn frozen_node_prevents_grant() {
        let root = Node::new_tree(());
        let frozen = root
            .clone()
            .bundle_new_structure_edit_prohibition()
            .expect("should success");
        assert!(matches!(
            root.tree().grant_structure_edit(),
            Err(StructureEditGrantError)
        ));

        drop(frozen);
        assert!(root.tree().grant_structure_edit().is_ok());
    }

    #[test]
    fn prohibition_prevents_hot_node_creation() {
        let root = Node::new_tree(());
        let prohibition = root
            .tree()
            .prohibit_structure_edit()
            .expect("should success");
        assert!(matches!(
            root.clone().bundle_new_structure_edit_grant(),
            Err(StructureEditGrantError)
        ));

        drop(prohibition);
        assert!(root.bundle_new_structure_edit_grant().is_ok());
    }

    #[test]
    fn prohibition_prevents_grant() {
        let root = Node::new_tree(());
        let prohibition = root
            .tree()
            .prohibit_structure_edit()
            .expect("should success");
        assert!(matches!(
            root.tree().grant_structure_edit(),
            Err(StructureEditGrantError)
        ));

        drop(prohibition);
        assert!(root.tree().grant_structure_edit().is_ok());
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

    #[test]
    fn hot_node_prevents_prohibition() {
        let root = Node::new_tree(());
        let hot = root
            .clone()
            .bundle_new_structure_edit_grant()
            .expect("should success");
        assert!(matches!(
            root.tree().prohibit_structure_edit(),
            Err(StructureEditProhibitionError)
        ));

        drop(hot);
        assert!(root.tree().prohibit_structure_edit().is_ok());
    }

    #[test]
    fn grant_prevents_frozen_node_creation() {
        let root = Node::new_tree(());
        let grant = root.tree().grant_structure_edit().expect("should success");
        assert!(matches!(
            root.clone().bundle_new_structure_edit_prohibition(),
            Err(StructureEditProhibitionError)
        ));

        drop(grant);
        assert!(root.bundle_new_structure_edit_prohibition().is_ok());
    }

    #[test]
    fn grant_prevents_prohibition() {
        let root = Node::new_tree(());
        let grant = root.tree().grant_structure_edit().expect("should success");
        assert!(matches!(
            root.tree().prohibit_structure_edit(),
            Err(StructureEditProhibitionError)
        ));

        drop(grant);
        assert!(root.tree().prohibit_structure_edit().is_ok());
    }
}
