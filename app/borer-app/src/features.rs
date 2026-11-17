//! The one registration list: every module that handles workspace-wide actions registers
//! them here, through [`crate::commands::register`], which keeps each in reach only while
//! its row's need is met.
//!
//! A new view adds one line to [`register`] (when it handles window-wide actions), its
//! [`crate::panels::PANELS`] row or [`crate::places::Place`] variant, and its
//! [`crate::commands::COMMANDS`] rows; nothing else outside its module.

use gpui::Entity;
use workspace::Workspace;

use crate::binary::Binary;

/// Registers every module's workspace-wide actions on `workspace`, over the window's
/// `binary`.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    crate::app_view::register(workspace, binary);
    crate::functions_panel::register(workspace, binary);
    crate::decompile_item::register(workspace, binary);
    crate::goto::register(workspace, binary);
    crate::overview::register(workspace, binary);
}
