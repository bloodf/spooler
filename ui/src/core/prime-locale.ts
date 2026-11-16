// PrimeVue's own labels (select filter and empty texts, dialog close…) in the languages the shared Orca UI
// foundation has no table for; English and Brazilian Portuguese come from the foundation.
import type { Locale } from './i18n-core';

type PrimeLabels = Record<string, unknown>;
export const primeLabels: Partial<Record<Locale, PrimeLabels>> = {
  es: {
    accept: 'Confirmar', reject: 'Volver', choose: 'Elegir', upload: 'Subir', cancel: 'Cancelar',
    emptyMessage: 'No hay elementos', emptyFilterMessage: 'Ningún resultado con estos filtros',
    emptySearchMessage: 'No se encontraron resultados', searchMessage: '{0} resultados encontrados',
    selectionMessage: '{0} elementos seleccionados', emptySelectionMessage: 'Ningún elemento seleccionado',
    dayNames: ['domingo', 'lunes', 'martes', 'miércoles', 'jueves', 'viernes', 'sábado'],
    dayNamesShort: ['dom', 'lun', 'mar', 'mié', 'jue', 'vie', 'sáb'], dayNamesMin: ['D', 'L', 'M', 'X', 'J', 'V', 'S'],
    monthNames: ['enero', 'febrero', 'marzo', 'abril', 'mayo', 'junio', 'julio', 'agosto', 'septiembre', 'octubre', 'noviembre', 'diciembre'],
    monthNamesShort: ['ene', 'feb', 'mar', 'abr', 'may', 'jun', 'jul', 'ago', 'sep', 'oct', 'nov', 'dic'],
    dateFormat: 'dd/mm/yy', firstDayOfWeek: 1,
    aria: { close: 'Cerrar', previous: 'Anterior', next: 'Siguiente', firstPageLabel: 'Primera página', lastPageLabel: 'Última página',
      nextPageLabel: 'Página siguiente', prevPageLabel: 'Página anterior', selectRow: 'Seleccionar fila', unselectRow: 'Deseleccionar fila' },
  },
  de: {
    accept: 'Bestätigen', reject: 'Zurück', choose: 'Auswählen', upload: 'Hochladen', cancel: 'Abbrechen',
    emptyMessage: 'Keine Einträge', emptyFilterMessage: 'Keine Ergebnisse für diese Filter',
    emptySearchMessage: 'Keine Ergebnisse gefunden', searchMessage: '{0} Ergebnisse gefunden',
    selectionMessage: '{0} Einträge ausgewählt', emptySelectionMessage: 'Kein Eintrag ausgewählt',
    dayNames: ['Sonntag', 'Montag', 'Dienstag', 'Mittwoch', 'Donnerstag', 'Freitag', 'Samstag'],
    dayNamesShort: ['So', 'Mo', 'Di', 'Mi', 'Do', 'Fr', 'Sa'], dayNamesMin: ['S', 'M', 'D', 'M', 'D', 'F', 'S'],
    monthNames: ['Januar', 'Februar', 'März', 'April', 'Mai', 'Juni', 'Juli', 'August', 'September', 'Oktober', 'November', 'Dezember'],
    monthNamesShort: ['Jan', 'Feb', 'Mär', 'Apr', 'Mai', 'Jun', 'Jul', 'Aug', 'Sep', 'Okt', 'Nov', 'Dez'],
    dateFormat: 'dd.mm.yy', firstDayOfWeek: 1,
    aria: { close: 'Schließen', previous: 'Zurück', next: 'Weiter', firstPageLabel: 'Erste Seite', lastPageLabel: 'Letzte Seite',
      nextPageLabel: 'Nächste Seite', prevPageLabel: 'Vorherige Seite', selectRow: 'Zeile auswählen', unselectRow: 'Zeile abwählen' },
  },
  'zh-CN': {
    accept: '确认', reject: '返回', choose: '选择', upload: '上传', cancel: '取消',
    emptyMessage: '没有项目', emptyFilterMessage: '没有符合这些筛选条件的结果',
    emptySearchMessage: '未找到结果', searchMessage: '找到 {0} 个结果',
    selectionMessage: '已选择 {0} 项', emptySelectionMessage: '未选择任何项',
    dayNames: ['星期日', '星期一', '星期二', '星期三', '星期四', '星期五', '星期六'],
    dayNamesShort: ['周日', '周一', '周二', '周三', '周四', '周五', '周六'], dayNamesMin: ['日', '一', '二', '三', '四', '五', '六'],
    monthNames: ['一月', '二月', '三月', '四月', '五月', '六月', '七月', '八月', '九月', '十月', '十一月', '十二月'],
    monthNamesShort: ['1月', '2月', '3月', '4月', '5月', '6月', '7月', '8月', '9月', '10月', '11月', '12月'],
    dateFormat: 'yy/mm/dd', firstDayOfWeek: 1,
    aria: { close: '关闭', previous: '上一个', next: '下一个', firstPageLabel: '第一页', lastPageLabel: '最后一页',
      nextPageLabel: '下一页', prevPageLabel: '上一页', selectRow: '选择行', unselectRow: '取消选择行' },
  },
};
